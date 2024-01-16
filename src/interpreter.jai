Variables :: struct {
    buffer   : []u8;
    bindings : Table(string, int);
}

Virtual_Machine :: struct {
    regs_top := 0; // index to top register
    vars_top := 0; // index to top of variable buffer
    // TODO: differentiate local and global scope
    bindings: Table(string, int); // name -> index to start in var_buf
    regs: [32]int;
    vars: [512]u8;
    // tape: []FWord;
}

interpret_program :: (program: *Program) -> bool {
    vm: Virtual_Machine;
    if !interpret_words(*vm, *program.words, program.loose) return false;
    
    words, ok := table_find(*program.words, "main");
    if !ok {
        log_error("you didn't define main!!!");
        return false;
    }
    
    return interpret_words(*vm, *program.words, words);
}

interpret_words :: (vm: *Virtual_Machine, dict: *FDict, ws: []FWord) -> bool {
    if !ws return true;
    ip := 0;
    while ip < ws.count {
        ip = interpret_word(vm, dict, ip, ws);
        if ip < 0 return false;
    }
    return true;
}

interpret_word :: (using vm: *Virtual_Machine, dict: *FDict, ip: int, words: []FWord) -> (new_ip: int) {
    word := *words[ip];
    // defer {
    //     xs: []int = .{regs_top, xx regs.data};
    //     log("\n%: % => %", ip, word.*, xs);
    // }
    if #complete word.type == {
    case .JMP; return word.as.jmp;
    case .JIZ; {
        if regs_top < 1 assert(false, "register stack underflow");
        regs_top -= 1;
        return ifx regs[regs_top] == 0 then word.as.jiz else ip + 1;
    }
    case .PUSH_INT; {
        if regs_top >= regs.count assert(false, "register stack overflow");
        regs[regs_top] = word.as.push_int;
        regs_top += 1;
        return ip + 1;
    }
    case .PUSH_STR; {
        if regs_top >= regs.count-1 assert(false, "register stack overflow");
        // TODO: copy into string storage and escape stuff
        regs[regs_top]   = word.as.push_str.count - 2;
        regs[regs_top+1] = cast,force(int) word.as.push_str.data + 1;
        regs_top += 2;
        return ip + 1;
    }
    case .ADD; {
        if regs_top < 2 assert(false, "register stack underflow");
        regs[regs_top-2] = regs[regs_top-2] + regs[regs_top-1];
        regs_top -= 1;
        return ip + 1;
    }
    case .DIV; {
        if regs_top < 2 assert(false, "register stack underflow");
        regs[regs_top-2] = regs[regs_top-2] / regs[regs_top-1];
        regs_top -= 1;
        return ip + 1;
    }
    case .GT; {
        if regs_top < 2 assert(false, "register stack underflow");
        regs[regs_top-2] = cast(int) (regs[regs_top-2] > regs[regs_top-1]);
        regs_top -= 1;
        return ip + 1;
    }
    case .LT; {
        if regs_top < 2 assert(false, "register stack underflow");
        regs[regs_top-2] = cast(int) (regs[regs_top-2] < regs[regs_top-1]); 
        regs_top -= 1;
        return ip + 1;
    }
    case .GET; {
        if regs_top < 1 assert(false, "register stack underflow");
        // TODO: types, register spreading for larger values
        // assert(false, "types duh %", word.as.get);
        if word.as.get.type != .STK {
            regs[regs_top-1] = (cast,force(*int) regs[regs_top-1]).*;         
        } else {
            regs_top -= 1;
            p := cast,force(*u8) regs[regs_top];
            for < word.as.get.as.stk {
                regs[regs_top] = (cast(*int)(p+it.offset)).*;
                // log("got %", regs[regs_top]);
                regs_top += 1;
            }
        }
        return ip + 1;
    }
    case .PUT; assert(false, "TODO: %", word); return -1;
    case .GET_VAR; {
        offset, ok := table_find(*bindings, word.as.get_var);
        assert(ok);
        regs[regs_top] = cast,force(int) *vars[offset];
        regs_top += 1;
        return ip + 1;
    }
    case .PUT_VAR; {
        if regs_top < 1 assert(false, "register stack underflow");
        if vars_top >= vars.count assert(false, "variable stack overflow");
        
        // NOTE: this means that we have shadowing semantics, may be a bad idea
        table_set(*bindings, word.as.put_var.name, vars_top);
        
        // TODO: write a nicer ice
        assert(word.as.put_var.type.count == 1);
        assert(word.as.put_var.type[0].type == .PUSH_TYPE);
        t := word.as.put_var.type[0].as.push_type;
        v := vars_top;
        if t.type != .STK {
            (cast(*int)(vars.data+vars_top)).* = regs[regs_top-1];
            vars_top += size_of(int);
            regs_top -= 1;
        } else for t.as.stk {
            (cast(*int)(vars.data+v+it.offset)).* = regs[regs_top-1];
            vars_top += runtime_size(t);
            regs_top -= 1;
        }
        return ip + 1;
    }
    case .ROT; {
        assert(word.as.rot > 0);
        if word.as.rot != 1 assert(false, "TODO");
        if regs_top < 2 assert(false, "register stack underflow");
        a := regs[regs_top-1];
        b := regs[regs_top-2];
        regs[regs_top-1] = b;
        regs[regs_top-2] = a;
        return ip + 1;
    }
    case .DUP; {
        assert(word.as.dup > 0);
        if regs_top < 1 assert(false, "register stack underflow");
        a := regs[regs_top-1];
        // assert(false, "%", word.as.dup);
        for 1..word.as.dup {
            // log("%", it);
            if regs_top >= regs.count assert(false, "register stack overflow");
            regs[regs_top] = a;
            regs_top += 1;
        }
        return ip + 1;
    }
    case .MACRO; {
        if !interpret_words(vm, dict, word.as.macro.call.body) return -1;
        return ip + 1;
    }
    case .CALL; {
        // log("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!");
        body, ok := table_find(dict, word.as.call);
        assert(ok, "TODO: error msg or maybe ice idk rn %", word.as.call);
        // TODO: local scope and stack traces maybe
        if !interpret_words(vm, dict, body) return -1;
        return ip + 1;
    }
    case .PUTC; {
        if regs_top < 1 assert(false, "register stack underflow");
        str: string = ---;
        str.count = 1;
        str.data  = cast(*u8) *regs[regs_top-1];
        write_string(str);
        regs_top -= 1;
        return ip + 1;
    }
    case .PUTI; {
        if regs_top < 1 assert(false, "register stack underflow");
        i := regs[regs_top-1];
        print("%", i);
        regs_top -= 1;
        return ip + 1;
    }
    case .PUTB; {
        if regs_top < 1 assert(false, "register stack underflow");
        i := regs[regs_top-1];
        write_string(ifx i == 0 then "false" else "true");
        regs_top -= 1;
        return ip + 1;
    }
    case .PUTA; {
        if regs_top < 1 assert(false, "register stack underflow");
        i := regs[regs_top-1];
        print("%", cast,force(*void) i);
        regs_top -= 1;
        return ip + 1;
    }
    case .PUTS; {
        if regs_top < 2 assert(false, "register stack underflow");
        str: string = ---;
        str.data  = (cast(**u8)*regs[regs_top-1]).*;
        str.count = regs[regs_top-2];
        regs_top -= 2;
        
        write_string(str);
        return ip + 1;
    }
    case .CASTT;      return ip + 1;
    case .SIZE_OF_TYPE;
        assert(false, "internal compiler error: unresolved type size %", word.as.size_of_type);
        return -1;
    case .NAME;
        assert(false, "internal compiler error: unresolved name %", word.as.name);
        return -1;
    case;
        assert(false, "corrupt word type %", cast(int) word.type);
        return -1;
    }
}
