To run dockerd, containerd, and runc **100% in pure Python without host kernel dependencies** , the modules you have provide the execution and AST-lowering pipeline to achieve full end-to-end emulation. 

Instead of talking to native Linux kernel subsystems (cgroups, namespaces, iptables, overlayfs, runc), **the translated Python code and Qiling framework act as the synthetic kernel** . 



<!-- Start of picture text -->
┌─────────────────────────────────────────────────────────────────────<br>────────┐<br>│                    Translated Go Code (Pure Python)<br>│<br>│  ┌────────────────────┐   ┌───────────────────────┐<br>┌──────────────────┐  │<br>│  │   dockerd (API)    │   │      containerd       │   │   runc / OCI<br>│  │<br>│  └─────────┬──────────┘   └───────────┬───────────┘<br>└────────┬─────────┘  │<br>│            │ gRPC over Memory Socket  │ gRPC / IPC             │<br>│<br>│            └──────────────────────────┴────────────────────────┘<br>│<br>├─────────────────────────────────────────────────────────────────────<br>────────┤<br>│                          Go Runtime Engine (Python)<br>│<br>│   goruntime.py (Sched/Channels) │ go_lower.py │ switch_case.py │<br>goto.py    │<br>├─────────────────────────────────────────────────────────────────────<br>────────┤<br>│                         Emulated Kernel Layer (Qiling)<br>│<br>│   ┌────────────────────┐   ┌───────────────────────┐<br>┌──────────────────┐  │<br>│   │ Virtual OverlayFS  │   │ Synthetic Network Stack│   │ Syscall<br>Emulator │  │<br>│   │ (Python File I/O)  │   │  (Userspace TCP/IP)   │   │  (Unicorn<br>CPU)   │  │<br>│   └────────────────────┘   └───────────────────────┘<br>└──────────────────┘  │<br>└─────────────────────────────────────────────────────────────────────<br>────────┘<br><!-- End of picture text -->

Here is how each layer is replaced in Python to cover every single base: 

# **1. Translating dockerd, containerd, and runc Source Code** 

Instead of calling external Linux binaries, you compile the original Go source code of moby/moby (dockerd), containerd/containerd, and opencontainers/runc directly into Python using your parser and lowering pass: 

● **AST Parsing & Lowering** : go_parser.py parses the Go files for all three daemons into 

ASTs, and go_lower.py transforms them into native Python modules. 

- **Concurrency Mechanics** : goruntime.py handles all internal goroutine scheduling, channel passing (make(chan)), select multiplexing, and mutexes natively within Python's runtime engine. 

- **Control Flow Control** : switch_case.py and goto.py maintain identical control-flow semantics for low-level runc logic and switch matching. 

- **In-Memory IPC** : dockerd talks to containerd via gRPC over Python in-memory unix domain sockets (asyncio or threading), eliminating external process execution completely. 

# **2. Covering the Subsystem Bases (Pure Python Replacements)** 

To remove background system dependencies (iptables, overlay2, systemd, cgroups, runc), <u>Qiling and Python stdlib modules synthesize all kernel responses:</u> 

|Native Dependency|Traditional Host Requirement|Pure Python & Qiling<br>Replacement|
|---|---|---|
|**runc (OCI Execution)**|Linux cgroups, namespaces,<br>clone(), pivot_root()|**Qiling CPU Engine**: Executes<br>the guest ELF binary inside an<br>emulated CPU context<br>(Unicorn) directly within the<br>Pythonprocess.|
|**overlay2 Storage**|Kernel overlay.ko module or<br>FUSE drivers|**Python Virtual RootFS**<br>**Overlay**: Python's shutil/pathlib<br>merges image tarball layers<br>into a local workspace directory<br>that Qiling maps as the<br>container's root(/).|
|**Networking & iptables**|Host veth bridges, NAT,<br>iptables rules|**Userspace TCP/IP Stack**:<br>Python hooks Qiling's socket<br>syscalls (sys_socket,<br>sys_connect, sys_bind) and<br>routes traffic using pure Python<br>networking libraries (like scapy<br>or lwipbindings).|
|**containerd-shim**|Process isolation to keep<br>container alive if daemon<br>restarts|**Python Thread/Task Wrapper**:<br>goruntime.go() spawns isolated<br>background threads with<br>Context cancellation handles to<br>monitor Qiling container state.|
|**Syscalls & Kernel ABI**|Host Linux Kernel (x86_64 /<br>ARM64)|**Qiling Syscall Interception**:<br>Container syscalls (sys_mmap,<br>sys_write, sys_execve) are<br>intercepted by Qiling Python<br>hooks and mapped to host<br>files/memory.|



# **3. Execution Flow in Pure Python** 

1. **API Call** : A docker run HTTP request hits the Python-translated dockerd REST router. 

2. **Image Unpacking** : Python downloads the OCI layers and unpacks them into a local directory (Virtual OverlayFS). 

3. **Container State** : Translated containerd receives the gRPC payload from dockerd over a Python memory pipe and tracks the container state via goruntime.py primitives. 

4. **Binary Execution** : Instead of calling runc to create cgroups/namespaces, translated runc invokes QilingBackend.start(), spinning up an emulated CPU worker in Python. 

5. **I/O Streaming** : Container stdout/stderr streams are captured directly from Qiling memory buffers and funneled back through goruntime.Channel pipelines to the dockerd HTTP response stream. 

By combining **AST code translation** for the Go daemons (dockerd, containerd, runc) with **Qiling's userspace CPU/syscall emulation** , you eliminate the need for host Linux kernel privileges, root access, or external background services entirely. 

