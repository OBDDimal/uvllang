// Instantiates libuvlparser.so (built for wasm32-emscripten, see
// docs/pyodide.md) as a bare WebAssembly module -- no Emscripten JS
// runtime, no Pyodide -- providing only the five import primitives any
// loader of a wasm dynamic-linking side module must supply (memory,
// indirect function table, stack pointer, memory/table base). This is
// what tests/test_pyodide_wasm.py shells out to: it proves the module
// itself is functionally correct (actually running the parse+CNF
// pipeline), independent of whether a real Pyodide/Emscripten loader is
// available to test against.
//
// Usage: node pyodide_smoke.mjs <path-to-libuvlparser.so> < uvl-source
// (source comes in on stdin, not argv, since real example models can
// exceed the OS argument-list size limit)
// Prints one JSON line to stdout: {"rc": 0, "dimacs": "..."} on success,
// or {"rc": <nonzero>, "error": "..."} on a real uvl_source_to_cnf failure.

import fs from "fs";

const [, , libPath] = process.argv;
const source = fs.readFileSync(0, "utf-8");

const buf = fs.readFileSync(libPath);
const memory = new WebAssembly.Memory({ initial: 256 }); // 16MB
const table = new WebAssembly.Table({ initial: 64, element: "anyfunc" });
const MEMORY_BASE = 1 << 20; // 1MB -- leaves 0..1MB as scratch space below
const __memory_base = new WebAssembly.Global({ value: "i32", mutable: false }, MEMORY_BASE);
const __table_base = new WebAssembly.Global({ value: "i32", mutable: false }, 1);
const __stack_pointer = new WebAssembly.Global({ value: "i32", mutable: true }, MEMORY_BASE - 4096);

const { instance } = await WebAssembly.instantiate(buf, {
  env: { memory, __indirect_function_table: table, __stack_pointer, __memory_base, __table_base },
});

// Required once after instantiation: patches data-section relocations
// against the real __memory_base (Emscripten's dynamic linker does this
// itself for a real side module load).
instance.exports.__wasm_apply_data_relocs();

// Output slots at a fixed low address; source text starts well above
// them (64KB in) so it can't grow into and corrupt them -- real example
// models run up to ~430KB, all comfortably under MEMORY_BASE (1MB).
const OUT_PTR_OFF = 0x100;
const OUT_LEN_OFF = 0x110;
const OUT_NB_OFF = 0x120;
const SRC_OFF = 0x10000;

const srcBytes = new TextEncoder().encode(source);
if (SRC_OFF + srcBytes.length > MEMORY_BASE) {
  throw new Error(`source too large for scratch region: ${srcBytes.length} bytes`);
}
new Uint8Array(memory.buffer, SRC_OFF, srcBytes.length).set(srcBytes);

// uvl_source_to_cnf(source_ptr, source_len, simplify, conversion,
//                    out_ptr, out_len, out_non_boolean) -> i32
new DataView(memory.buffer).setInt32(OUT_PTR_OFF, 0, true);

const rc = instance.exports.uvl_source_to_cnf(
  SRC_OFF, srcBytes.length,
  0, 0,
  OUT_PTR_OFF, OUT_LEN_OFF, OUT_NB_OFF,
);

// memory.buffer may have been detached and replaced if the call grew
// memory (page_allocator does this via @wasmMemoryGrow) -- re-fetch it.
const view = new DataView(memory.buffer);
const mem8 = new Uint8Array(memory.buffer);

if (rc === 0) {
  const outPtr = view.getInt32(OUT_PTR_OFF, true);
  const outLen = view.getInt32(OUT_LEN_OFF, true);
  const dimacs = new TextDecoder().decode(mem8.slice(outPtr, outPtr + outLen));
  console.log(JSON.stringify({ rc, dimacs }));
} else {
  const errPtr = instance.exports.uvl_last_error();
  let end = errPtr;
  while (mem8[end] !== 0 && end < errPtr + 1024) end++;
  const error = new TextDecoder().decode(mem8.slice(errPtr, end));
  console.log(JSON.stringify({ rc, error }));
}
