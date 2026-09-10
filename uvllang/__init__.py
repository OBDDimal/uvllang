def __getattr__(name):
    # Lazy: `.uvl` pulls in pysat at import time (~13-40ms), real cost on
    # tiny models. Importing any other uvllang submodule (e.g.
    # `from uvllang import _zig`) must not pay for that, so UVL is only
    # loaded on first actual access.
    if name == "UVL":
        from .uvl import UVL

        return UVL
    raise AttributeError(f"module {__name__!r} has no attribute {name!r}")
