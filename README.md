# Why not use golang code in a compiled format and just link it via ctypes in Python?

Integration and direct access. the code is designed to allow for translation of code before direct use in python.<br><br>
Because the runtime was written on top of python3.6 to python3.10 logic, it is compatible with 99% of devices.

# Why not just compile down or use subprocesses? Wouldn't that be simpler?

This project is designed to run without the need for any compiler process or subprocessing.<br><br>Why compile when you can not?

# How do I use the code?

`translate_go` and python's `exec` with `globals()` as its second parameter.<br> Or rather `exec(translate_go({quoted golang go here}, import_paths["import path 1"]), globals())`

<br><br>From there, all golang code are usable, directly within the python pipeline.
