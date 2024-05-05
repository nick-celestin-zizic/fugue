// Variables :: struct {
//     buffer   : []u8;
//     bindings : Table(string, int);
// }

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

interpret_words :: (vm: *Virtual_Machine, dict: *FDict, ws: []FWord, timeout_seconds := 5.0) -> bool {
    if !ws return true;
    start := current_time_seconds();
    ip := 0;
    while ip < ws.count {
        ip = interpret_word(vm, dict, ip, ws);
        if ip < 0 return false;
        if (current_time_seconds() - start) > timeout_seconds {
            log_error("Program timed out!");
            return false;
        }
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
    case .HOLE; return ip + 1; // no-op
    case .JMP; return word.as.jmp;
    case .JIF; {
        if regs_top < 1 assert(false, "register stack underflow");
        regs_top -= 1;
        return ifx regs[regs_top] == 0 then word.as.jif else ip + 1;
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
        // log("PUSH_STR(%)", word.as.push_str);
        regs[regs_top]   = word.as.push_str.count - 2;
        regs[regs_top+1] = cast,force(int) (word.as.push_str.data + 1);
        
        regs_top += 2;
        return ip + 1;
    }
    case .ADD; {
        if regs_top < 2 assert(false, "register stack underflow");
        regs[regs_top-2] = regs[regs_top-2] + regs[regs_top-1];
        regs_top -= 1;
        return ip + 1;
    }
    case .SUB; {
        if regs_top < 2 assert(false, "register stack underflow");
        regs[regs_top-2] = regs[regs_top-2] - regs[regs_top-1];
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
        // push :: (t: *FType, data: *u8, vars_top: *int, regs_top: *int, regs: []int) {
        size := runtime_size(t);
        if t.type == .STK {
            push_type_stack_onto_variable_stack_from_register_stack(vm, t.as.stk);
            vars_top += size;
        } else {
            assert(size <= size_of(int));
            memcpy(vars.data+vars_top, *regs[regs_top-1], size);
            vars_top += size;
            regs_top -= 1;
        }
        // }
        // push(t, vars.data, *vars_top, *regs_top, regs);
        return ip + 1;
    }
    case .ROT; {
        assert(word.as.rot > 0);
        assert(regs_top >= word.as.rot+1, "register stack underflow % %", regs_top, word.as.rot);
        if word.as.rot == 1 {
            a := regs[regs_top-1];
            b := regs[regs_top-2];
            regs[regs_top-1] = b;
            regs[regs_top-2] = a;
        } else {
            rs: []int = .{regs_top, xx regs.data};
            begin := rs.count-1-word.as.rot;
            first := rs[begin];
            for begin..rs.count-2 rs[it] = rs[it+1];
            rs[rs.count-1] = first;
        }
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
    case .DROP; {
        assert(word.as.drop >= 1);
        for 1..word.as.dup {
            if regs_top < 1 assert(false, "register stack underflow");
            regs_top -= 1;
        }
        return ip + 1;
    }
    case .OVER; {
        if regs_top >= regs.count assert(false, "register stack overflow");
        regs[regs_top] = regs[regs_top-1-word.as.over];
        regs_top += 1;
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
        append(*output, str);
        regs_top -= 1;
        return ip + 1;
    }
    case .PUTI; {
        if regs_top < 1 assert(false, "register stack underflow");
        i := regs[regs_top-1];
        print_to_builder(*output, "%", i);
        regs_top -= 1;
        return ip + 1;
    }
    case .PUTB; {
        if regs_top < 1 assert(false, "register stack underflow");
        i := regs[regs_top-1];
        append(*output, ifx i == 0 then "false" else "true");
        regs_top -= 1;
        return ip + 1;
    }
    case .PUTA; {
        if regs_top < 1 assert(false, "register stack underflow");
        i := regs[regs_top-1];
        print_to_builder(*output, "%", cast,force(*void) i);
        regs_top -= 1;
        return ip + 1;
    }
    case .PUTS; {
        if regs_top < 2 assert(false, "register stack underflow");
        str: string = ---;
        str.data  = (cast(**u8)*regs[regs_top-1]).*;
        str.count = regs[regs_top-2];
        regs_top -= 2;
        
        append(*output, str);
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

// WARNING: it is on you to vars_top += size; after calling this because i don't want to make another wrapper for the recursion
push_type_stack_onto_variable_stack_from_register_stack :: (using vm: *Virtual_Machine, stk: Type_Stack) {
    for < stk {
        if it.type.type == .STK {
            PushState(vars_top, vars_top+it.offset);
            push_type_stack_onto_variable_stack_from_register_stack(vm, it.type.as.stk);
        } else {
            // TODO: sanity check for buffer overrun
            assert(vars.data+vars_top+it.offset < xx (vars.data+vars.count));
            memcpy(vars.data+vars_top+it.offset, *regs[regs_top-1], runtime_size(it.type));
            regs_top -= 1;
        }
    }
}
