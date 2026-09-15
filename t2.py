from __future__ import annotations

import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
MOBY_ROOT = HERE / "moby-master"
GOROOT_SRC = Path("/usr/local/go/src")
GOROOT_VENDOR = GOROOT_SRC / "vendor"
MOBY_VENDOR = MOBY_ROOT / "vendor"

if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

import go_lower
from go_lower import load_go_package, translate_go
from go_parser import parse_go

def translate_dockerd_entrypoint():
    main_go = MOBY_ROOT / "cmd" / "dockerd" / "main.go"
    source = main_go.read_text(encoding="utf-8")
    python_code = translate_go(
        source,
        module_name="dockerd_main",
        import_paths=[str(MOBY_ROOT), str(MOBY_VENDOR), str(GOROOT_SRC), str(GOROOT_VENDOR)],
    )
    compile(python_code, str(main_go), "exec")
    # Compile the emitted entrypoint here.  Executing it immediately would
    # recursively import the complete Go stdlib before we have separately
    # tested the filesystem package loader.
    compile(python_code, str(main_go), "exec")
    return python_code


def main() -> int:
    if not (MOBY_ROOT / "go.mod").exists():
        raise RuntimeError(f"Moby source tree not found at {MOBY_ROOT}")

    print("[3/4] Moby cmd/dockerd/main.go translate + compile + exec")
    entrypoint = translate_dockerd_entrypoint()
    exec(entrypoint, globals(), globals())
    print(dir())

if __name__ == "__main__":
    raise SystemExit(main())
