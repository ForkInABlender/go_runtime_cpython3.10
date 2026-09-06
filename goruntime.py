"""goruntime.py -- Go runtime primitives implemented in pure Python (Layer A)."""

from __future__ import annotations

import collections
import concurrent.futures
import contextlib
import contextvars
import dataclasses
import queue
import random
import threading
import time
import weakref
from typing import Any, Callable, Dict, Generic, Iterator, List, Optional, Protocol, Tuple, TypeVar


_T = TypeVar("_T")

# ============================================================================
# Go Runtime -- scheduler
# ============================================================================

class _Runtime:
    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._gomaxprocs = 4
        self._executor: Optional[concurrent.futures.ThreadPoolExecutor] = None
        self._gid_counter = 0

    def _ensure_executor(self) -> concurrent.futures.ThreadPoolExecutor:
        with self._lock:
            if self._executor is None or getattr(self._executor, "_shutdown", False):
                self._executor = concurrent.futures.ThreadPoolExecutor(
                    max_workers=self._gomaxprocs, thread_name_prefix="goroutine",
                )
            return self._executor

    def GOMAXPROCS(self, n: Optional[int] = None) -> int:
        with self._lock:
            if n is not None and n > 0:
                self._gomaxprocs = n
                if self._executor is not None:
                    self._executor.shutdown(wait=False)
                    self._executor = None
            return self._gomaxprocs

    def go(self, fn: Callable[..., Any], *args: Any, **kwargs: Any) -> "G":
        executor = self._ensure_executor()
        with self._lock:
            self._gid_counter += 1
            gid = self._gid_counter
        def _run() -> None:
            _current_g.set(gid)
            try:
                fn(*args, **kwargs)
            except Exception:
                import traceback
                traceback.print_exc()
        future = executor.submit(_run)
        return G(gid, future)

_runtime = _Runtime()
_current_g: contextvars.ContextVar[int] = contextvars.ContextVar("_current_g")

def go(fn: Callable[..., Any], *args: Any, **kwargs: Any) -> "G":
    return _runtime.go(fn, *args, **kwargs)

def GOMAXPROCS(n: Optional[int] = None) -> int:
    return _runtime.GOMAXPROCS(n)

class G:
    def __init__(self, gid: int, future: concurrent.futures.Future) -> None:
        self.gid = gid
        self._future = future
    def join(self) -> None:
        self._future.result()

# ============================================================================
# Channels
# ============================================================================

class ChannelClosed(Exception):
    pass

_CHANNEL_SENTINEL = object()

class Channel(Generic[_T]):
    def __init__(self, capacity: int = 0) -> None:
        if capacity < 0:
            raise ValueError("capacity must be >= 0")
        self._cap = capacity
        self._q: queue.Queue[Optional[_T]] = queue.Queue(maxsize=max(1, capacity))
        self._closed = False
        self._lock = threading.Lock()

    def send(self, value: _T) -> None:
        with self._lock:
            if self._closed:
                raise ChannelClosed("send on closed channel")
        self._q.put(value)

    def recv(self) -> _T:
        while True:
            try:
                val = self._q.get(timeout=0.1)
                with self._lock:
                    if self._closed and val is _CHANNEL_SENTINEL:
                        raise ChannelClosed("receive on closed channel")
                return val  # type: ignore
            except queue.Empty:
                with self._lock:
                    if self._closed:
                        raise ChannelClosed("receive on closed channel")

    def try_recv(self) -> Tuple[bool, Optional[_T]]:
        try:
            val = self._q.get_nowait()
            with self._lock:
                if self._closed and val is _CHANNEL_SENTINEL:
                    return False, None
            return True, val
        except queue.Empty:
            return False, None

    def try_send(self, value: _T) -> bool:
        try:
            self._q.put_nowait(value)
            return True
        except queue.Full:
            return False

    def close(self) -> None:
        with self._lock:
            if self._closed:
                raise ChannelClosed("close of closed channel")
            self._closed = True
        try:
            self._q.put_nowait(_CHANNEL_SENTINEL)
        except queue.Full:
            pass

    def __iter__(self) -> Iterator[_T]:
        while True:
            try:
                yield self.recv()
            except ChannelClosed:
                break

    def __len__(self) -> int:
        return self._q.qsize()

    @property
    def capacity(self) -> int:
        return self._cap

def make_chan(_type=None, capacity: int = 0) -> Channel:
    return Channel(capacity=capacity)

# ============================================================================
# Select
# ============================================================================

@dataclasses.dataclass
class _Case:
    kind: str
    ch: Optional[Channel] = None
    value: Any = None
    callback: Optional[Callable] = None

def case_recv(ch: Channel[_T], callback: Callable[[_T], Any]) -> _Case:
    return _Case(kind="recv", ch=ch, callback=callback)

def case_send(ch: Channel[_T], value: _T, callback: Optional[Callable[[], Any]] = None) -> _Case:
    return _Case(kind="send", ch=ch, value=value, callback=callback)

def case_default(callback: Callable[[], Any]) -> _Case:
    return _Case(kind="default", callback=callback)

def select(*cases: _Case) -> None:
    """Select one ready communication, otherwise use default, otherwise wait."""
    cases = list(cases)
    if not cases:
        return
    non_default = [c for c in cases if c.kind != "default"]
    order = list(range(len(non_default)))

    def probe() -> bool:
        random.shuffle(order)
        for idx in order:
            case = non_default[idx]
            if case.kind == "recv":
                ok, val = case.ch.try_recv()  # type: ignore[union-attr]
                if ok:
                    case.callback(val)  # type: ignore[misc]
                    return True
            elif case.kind == "send":
                if case.ch.try_send(case.value):  # type: ignore[union-attr]
                    if case.callback is not None:
                        case.callback()
                    return True
        return False

    # Go's default case is eligible only when no communication is ready.
    if probe():
        return
    defaults = [c for c in cases if c.kind == "default"]
    if defaults:
        defaults[0].callback()  # type: ignore[misc]
        return

    deadline = time.time() + 10.0
    while time.time() < deadline:
        if probe():
            return
        time.sleep(0.001)

# ============================================================================
# Sync
# ============================================================================

class Mutex:
    def __init__(self):
        self._lock = threading.Lock()
    def lock(self):
        self._lock.acquire()
    def unlock(self):
        self._lock.release()
    def __enter__(self):
        self.lock()
        return self
    def __exit__(self, *args):
        self.unlock()

class RWMutex:
    def __init__(self):
        self._w = threading.Lock()
        self._m = threading.Lock()
        self._reader_count = 0
    def rlock(self):
        self._m.acquire()
        self._reader_count += 1
        if self._reader_count == 1:
            self._w.acquire()
        self._m.release()
    def runlock(self):
        self._m.acquire()
        self._reader_count -= 1
        if self._reader_count == 0:
            self._w.release()
        self._m.release()
    def lock(self):
        self._w.acquire()
    def unlock(self):
        self._w.release()
    def __enter__(self):
        self.lock()
        return self
    def __exit__(self, *args):
        self.unlock()

class WaitGroup:
    def __init__(self):
        self._count = 0
        self._cond = threading.Condition()
    def add(self, delta=1):
        with self._cond:
            self._count += delta
            if self._count < 0:
                raise ValueError("negative WaitGroup counter")
    def done(self):
        with self._cond:
            self._count -= 1
            if self._count == 0:
                self._cond.notify_all()
            elif self._count < 0:
                raise ValueError("negative WaitGroup counter")
    def wait(self):
        with self._cond:
            while self._count > 0:
                self._cond.wait()

class Once:
    def __init__(self):
        self._done = False
        self._lock = threading.Lock()
    def do(self, fn):
        if self._done:
            return
        with self._lock:
            if not self._done:
                fn()
                self._done = True

class Cond:
    def __init__(self, locker=None):
        self._lock = (locker or Mutex())._lock
        self._cond = threading.Condition(self._lock)
    def wait(self):
        self._cond.wait()
    def signal(self):
        self._cond.notify()
    def broadcast(self):
        self._cond.notify_all()

class Pool(Generic[_T]):
    def __init__(self, new: Callable[[], _T]):
        self._new = new
        self._pool: collections.deque[_T] = collections.deque()
        self._lock = threading.Lock()
    def get(self) -> _T:
        with self._lock:
            if self._pool:
                return self._pool.popleft()
        return self._new()
    def put(self, x: _T):
        with self._lock:
            self._pool.append(x)

# ============================================================================
# Context
# ============================================================================

class Context:
    def __init__(self, parent=None, cancel_event=None, deadline=None):
        self._parent = parent
        self._cancel_event = cancel_event or threading.Event()
        self._deadline = deadline
        self._values: Dict[Any, Any] = {}
        self._children: weakref.WeakSet[Context] = weakref.WeakSet()
        self._lock = threading.Lock()
        if parent is not None:
            parent._children.add(self)
    def deadline(self):
        if self._deadline is not None:
            return True, self._deadline
        if self._parent is not None:
            return self._parent.deadline()
        return False, None
    def done(self):
        return self._cancel_event
    def err(self):
        if self._cancel_event.is_set():
            if self._deadline is not None and time.time() > self._deadline:
                return TimeoutError("context deadline exceeded")
            return RuntimeError("context canceled")
        return None
    def value(self, key):
        with self._lock:
            if key in self._values:
                return self._values[key]
        if self._parent is not None:
            return self._parent.value(key)
        return None
    def with_value(self, key, val):
        child = Context(parent=self)
        child._values[key] = val
        return child
    def _cancel(self, err=None):
        self._cancel_event.set()
        for child in list(self._children):
            child._cancel(err)
    def __enter__(self):
        return self
    def __exit__(self, *args):
        self._cancel()

def background():
    return Context()

def todo():
    return Context()

def with_cancel(parent):
    child = Context(parent=parent)
    return child, lambda: child._cancel()

def with_timeout(parent, seconds):
    deadline = time.time() + seconds
    child = Context(parent=parent, deadline=deadline)
    def _timer():
        remaining = deadline - time.time()
        if remaining > 0:
            time.sleep(remaining)
        if not child.done().is_set():
            child._cancel()
    threading.Thread(target=_timer, daemon=True).start()
    return child, lambda: child._cancel()

def with_value(parent, key, val):
    return parent.with_value(key, val)

# ============================================================================
# Atomic
# ============================================================================

class AtomicInt64:
    def __init__(self, val=0):
        self._val = val
        self._lock = threading.Lock()
    def load(self):
        with self._lock:
            return self._val
    def store(self, val):
        with self._lock:
            self._val = val
    def add(self, delta=1):
        with self._lock:
            self._val += delta
            return self._val
    def compare_and_swap(self, old, new):
        with self._lock:
            if self._val == old:
                self._val = new
                return True
            return False

class AtomicBool:
    def __init__(self, val=False):
        self._val = val
        self._lock = threading.Lock()
    def load(self):
        with self._lock:
            return self._val
    def store(self, val):
        with self._lock:
            self._val = val

# ============================================================================
# Timer / Ticker
# ============================================================================

class Timer:
    def __init__(self, seconds, callback):
        self._timer = threading.Timer(seconds, callback)
        self._timer.start()
    def stop(self):
        return self._timer.cancel()

class Ticker:
    def __init__(self, seconds):
        self._seconds = seconds
        self._ch = make_chan(bool, 1)
        self._stop_event = threading.Event()
        self._thread = threading.Thread(target=self._run, daemon=True)
        self._thread.start()
    def _run(self):
        while not self._stop_event.is_set():
            time.sleep(self._seconds)
            if not self._stop_event.is_set():
                try:
                    self._ch.send(True)
                except ChannelClosed:
                    break
    def c(self):
        return self._ch
    def stop(self):
        self._stop_event.set()
        self._ch.close()

# ============================================================================
# Defer / Panic / Recover
# ============================================================================

class _DeferFrame:
    def __init__(self):
        self._stack = []
        self._lock = threading.Lock()
    def defer(self, fn):
        with self._lock:
            self._stack.append(fn)
    def run(self, exc=None):
        with self._lock:
            while self._stack:
                fn = self._stack.pop()
                try:
                    fn()
                except Exception:
                    import traceback
                    traceback.print_exc()
        return exc

_defer_local = threading.local()

def _current_frame():
    if not hasattr(_defer_local, "frame"):
        _defer_local.frame = _DeferFrame()
    return _defer_local.frame

def defer(fn):
    _current_frame().defer(fn)

@contextlib.contextmanager
def gofunc():
    frame = _DeferFrame()
    old = getattr(_defer_local, "frame", None)
    _defer_local.frame = frame
    try:
        yield
    except BaseException as e:
        frame.run(e)
        raise
    finally:
        frame.run()
        _defer_local.frame = old

# ============================================================================
# Interfaces
# ============================================================================

class Stringer(Protocol):
    def String(self) -> str: ...

class Error(Protocol):
    def Error(self) -> str: ...

class Reader(Protocol):
    def Read(self, n: int) -> bytes: ...

class Writer(Protocol):
    def Write(self, data: bytes) -> int: ...
