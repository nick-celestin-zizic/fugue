let jai_context;         // thread local storage used by jai runtime
let allocated;           // wasm memory (used to look up pointers)
let exports;             // wasm procedures
let resolved_procs = {}; // demangled name -> procedure
let tallocated_address;  // used by talloc_reg and wasm_set_tallocated

// These are all the functions that we declared as "#foreign" in our Jai code.
// They let you interact with the JS and DOM world from within Jai.
// If you forget to implement one, the Proxy below will log a nice error.
const exported_js_functions = {
    wasm_write_string: (s_count, s_data, to_standard_error) => {
        const string = to_js_string(s_data, s_count);
        write_to_console_log(string, to_standard_error);
    },
    wasm_debug_break: () => { debugger; },
    wasm_log_dom: (s_count, s_data, is_error) => {
        const log = document.querySelector("#log");
        const string = to_js_string(s_data, s_count);
        const lines = string.split("\n");
        for (let i = 0; i < lines.length; i++) {
            const line = lines[i];
            if (!line && i == lines.length - 1) continue; // Don’t create an extra empty line after the last newline

            const element = document.createElement("div");
            if (is_error) element.style.color = "#d33";
            element.innerText = line;
            log.appendChild(element);
        }
    },
    wasm_set_tallocated: (p) => { tallocated_address = BigInt(p) },
    memcmp: (a, b, count) => {
        const u8 = new Uint8Array(allocated.buffer)
        const buf_a = u8.subarray(Number(a), Number(a) + Number(count));
        const buf_b = u8.subarray(Number(b), Number(b) + Number(count));
        for (let i = 0; i < count; i++) {
            const delta = Number(buf_a[i]) - Number(buf_b[i]);
            if (delta !== 0) return delta;
        }
        return 0;
    }
}

// Create the environment for the WASM file,
// which includes the exported JS functions for the WASM:
const imports = {
    "env": new Proxy(exported_js_functions, {
        get(target, prop, receiver) {
            if (target.hasOwnProperty(prop)) return target[prop];
            return () => { throw new Error("Missing function: " + prop); };
        },
    }),
}

// Load the WASM file we compiled and run its main.
let types = {};
const wasmInstance = WebAssembly.instantiateStreaming(fetch("main.wasm"), imports)
    .then((obj) => {
        exports       = obj.instance.exports;
        allocated     = exports.memory;
        jai_context   = BigInt(exports.__jai_runtime_init(0, BigInt(0)));
        console.log(exports);
    }
);

function call_wasm(name, ...arguments) {
    const proc = find_export(name);
    const args = arguments.map((x) => typeof(x) === "string" ? to_jai_string(x) : x);
    const num  = proc.length-args.length-1;
    const rets = call_wasm_procedure(
        proc, (num > 0) ? find_type_info(name, num) : [], ...args
    );
    find_export("reset_temporary_storage")(jai_context);
    return rets;
}

function find_export(name) {
    let proc = resolved_procs[name];
    if (proc === undefined) {
        const re = new RegExp('^'+name+'_[0-9a-z]+$');
        for (let full_name in exports) if (re.test(full_name)) {
            resolved_procs[name] = exports[full_name];
            proc = exports[full_name];
            break;
        }
    }
    
    if (proc === undefined) {
        console.error("wasm procedure", name, "does not exist!");
        return;
    }
    
    return proc;
}

function find_type_info(name, num_rets) {
    info = types[name];
    if (info !== undefined) return info;
    info = []; // only return types as of now
    const max_rets = BigInt(256);
    const treg = find_export("talloc_reg");
    const ident = name+"_ret_type";
    const proc = find_export(ident);
    if (proc === undefined) {
        console.error("could not find type info for", name, "(add @JsExport to the end of the procedure)");
        return;
    }
    for (let i = BigInt(0); i < BigInt(num_rets); i++) {
        tallocated_address = undefined;
        treg(jai_context);
        proc(jai_context, i, tallocated_address);
        info.push(copy_jai_memory(tallocated_address, 8).getBigInt64());
    }
    types[name] = info;
    return info;
}

function copy_jai_memory(addr, size) {
    return (new DataView((new Uint8Array(
        allocated.buffer.slice(Number(addr), Number(addr) + size)
    ).reverse()).buffer, 0));
}

function call_wasm_procedure(proc, type, ...args) {
    if (args.length < proc.length-1) {
        rets = [];
        treg = find_export("talloc_reg");
        for (let i = 0; i < proc.length-args.length-1; i++) {
            tallocated_address = undefined;
            treg(jai_context);
            rets.push(tallocated_address);
        }
        proc(jai_context, ...args, ...rets);
        
        fin = rets.map((ptr, index) => {
            if (type[index] === TYPE_STRING) {
                const mem   = copy_jai_memory(ptr, 16);
                const data  = mem.getBigInt64();
                const count = mem.getBigInt64(8);
                return to_js_string(data, count);
            } else if (type[index] == TYPE_BOOL) {
                return copy_jai_memory(ptr, 8).getBigInt64() ? true : false;
            } else {
                const mem = copy_jai_memory(ptr, 8);
                return mem.getBigInt64();
            }
        });
        
        return (fin.length === 1) ? fin[0] : fin;
    } else {
        proc(jai_context, ...args);
    }
}

const TYPE_ADDR    = BigInt(0);
const TYPE_INT     = BigInt(1);
const TYPE_BIG_INT = BigInt(2);
const TYPE_STRING  = BigInt(3);
const TYPE_BOOL    = BigInt(4);

const text_decoder = new TextDecoder();
function to_js_string(pointer, length) {
    const u8 = new Uint8Array(allocated.buffer)
    const bytes = u8.subarray(Number(pointer), Number(pointer) + Number(length));
    return text_decoder.decode(bytes);
}

function talloc(bytes) {
    const size = BigInt(bytes);
    const proc = find_export("talloc");
    proc(jai_context, size, tallocated_address);
    return copy_jai_memory(tallocated_address, 8).getBigInt64();
}

function to_jai_string(str) {
    if (str !== null && str !== undefined && str !== 0) {
        // out parameter for talloc and
        find_export("talloc_reg")(jai_context);
        
        // allocate space for string
        // at most 4 bytes per UTF-8 code point
        let count = BigInt(str.length << 2);
        find_export("talloc")(jai_context, count, tallocated_address);
        const data = copy_jai_memory(tallocated_address, 8).getBigInt64();
        count = BigInt(stringToUTF8(str, data, count));
        
        // construct the string, also uses temporary storage
        find_export("make_string")(jai_context, count, data, tallocated_address);
        return copy_jai_memory(tallocated_address, 8).getBigInt64();
    }
    return BigInt(0);
}

// from: https://github.com/elvis-epx/emscripten-example/blob/master/c_module.js#L781
function stringToUTF8(str, outPtr, maxBytesToWrite) {
  return stringToUTF8Array(str, new Uint8Array(allocated.buffer), outPtr, BigInt(maxBytesToWrite));
}
function stringToUTF8Array(str, outU8Array, outIdx, maxBytesToWrite) {
  if (!(maxBytesToWrite > 0)) // Parameter maxBytesToWrite is not optional. Negative values, 0, null, undefined and false each don't write out any bytes.
    return 0;

  var startIdx = outIdx;
  var endIdx = outIdx + maxBytesToWrite - BigInt(1); // -1 for string null terminator.
  for (var i = 0; i < str.length; ++i) {
    // Gotcha: charCodeAt returns a 16-bit word that is a UTF-16 encoded code unit, not a Unicode code point of the character! So decode UTF16->UTF32->UTF8.
    // See http://unicode.org/faq/utf_bom.html#utf16-3
    // For UTF8 byte structure, see http://en.wikipedia.org/wiki/UTF-8#Description and https://www.ietf.org/rfc/rfc2279.txt and https://tools.ietf.org/html/rfc3629
    var u = str.charCodeAt(i); // possibly a lead surrogate
    if (u >= 0xD800 && u <= 0xDFFF) {
      var u1 = str.charCodeAt(++i);
      u = 0x10000 + ((u & 0x3FF) << 10) | (u1 & 0x3FF);
    }
    if (u <= 0x7F) {
      if (outIdx >= endIdx) break;
      outU8Array[outIdx++] = u;
    } else if (u <= 0x7FF) {
      if (outIdx + 1 >= endIdx) break;
      outU8Array[outIdx++] = 0xC0 | (u >> 6);
      outU8Array[outIdx++] = 0x80 | (u & 63);
    } else if (u <= 0xFFFF) {
      if (outIdx + 2 >= endIdx) break;
      outU8Array[outIdx++] = 0xE0 | (u >> 12);
      outU8Array[outIdx++] = 0x80 | ((u >> 6) & 63);
      outU8Array[outIdx++] = 0x80 | (u & 63);
    } else if (u <= 0x1FFFFF) {
      if (outIdx + 3 >= endIdx) break;
      outU8Array[outIdx++] = 0xF0 | (u >> 18);
      outU8Array[outIdx++] = 0x80 | ((u >> 12) & 63);
      outU8Array[outIdx++] = 0x80 | ((u >> 6) & 63);
      outU8Array[outIdx++] = 0x80 | (u & 63);
    } else if (u <= 0x3FFFFFF) {
      if (outIdx + 4 >= endIdx) break;
      outU8Array[outIdx++] = 0xF8 | (u >> 24);
      outU8Array[outIdx++] = 0x80 | ((u >> 18) & 63);
      outU8Array[outIdx++] = 0x80 | ((u >> 12) & 63);
      outU8Array[outIdx++] = 0x80 | ((u >> 6) & 63);
      outU8Array[outIdx++] = 0x80 | (u & 63);
    } else {
      if (outIdx + 5 >= endIdx) break;
      outU8Array[outIdx++] = 0xFC | (u >> 30);
      outU8Array[outIdx++] = 0x80 | ((u >> 24) & 63);
      outU8Array[outIdx++] = 0x80 | ((u >> 18) & 63);
      outU8Array[outIdx++] = 0x80 | ((u >> 12) & 63);
      outU8Array[outIdx++] = 0x80 | ((u >> 6) & 63);
      outU8Array[outIdx++] = 0x80 | (u & 63);
    }
  }
  // Null-terminate the pointer to the buffer.
  outU8Array[outIdx] = 0;
  return outIdx - startIdx;
}


// console.log and console.error always add newlines so we need to buffer the output from write_string
// to simulate a more basic I/O behavior. We’ll flush it after a certain time so that you still
// see the last line if you forget to terminate it with a newline for some reason.
let console_buffer = "";
let console_buffer_is_standard_error;
let console_timeout;
const FLUSH_CONSOLE_AFTER_MS = 3;

function write_to_console_log(str, to_standard_error) {
    if (console_buffer && console_buffer_is_standard_error != to_standard_error) {
        flush_buffer();
    }

    console_buffer_is_standard_error = to_standard_error;
    const lines = str.split("\n");
    for (let i = 0; i < lines.length - 1; i++) {
        console_buffer += lines[i];
        flush_buffer();
    }

    console_buffer += lines[lines.length - 1];

    clearTimeout(console_timeout);
    if (console_buffer) {
        console_timeout = setTimeout(() => {
            flush_buffer();
        }, FLUSH_CONSOLE_AFTER_MS);
    }

    function flush_buffer() {
        if (!console_buffer) return;

        if (console_buffer_is_standard_error) {
            console.error(console_buffer);
        } else {
            console.log(console_buffer);
        }

        console_buffer = "";
    }
}
