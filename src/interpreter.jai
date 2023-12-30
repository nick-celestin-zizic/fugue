Variables :: struct {
    buffer   : []u8;
    bindings : Table(string, int);
}

Virtual_Machine :: struct {
    regs_top := 0; // index to top register
    vars_top := 0; // index to top of variable buffer
    bindings: Table(string, int); // name -> index to start in var_buf
    ip := 0;
    regs: [32]int;
    vars: [512]u8;
}

interpret_program :: (program: *Program) -> bool {
    vm: Virtual_Machine;
    while true {
        interpret_word(*vm, program, program.loose[vm.ip]);
        if vm.ip <  0 return false;
        if vm.ip >= program.loose.count break;
    }
    
    vm.ip = 0;
    words, ok := table_find(*program.words, "main");
    if !ok {
        log_error("you didn't define main!!!");
        return false;
    }
    
    while true {
        interpret_word(*vm, program, words[vm.ip]);
        if vm.ip <  0 return false;
        if vm.ip >= words.count break;
    }
    
    return true;
}

interpret_word :: (using vm: *Virtual_Machine, program: *Program, word: Word) {
    // defer {
    //     r: []int = ---;
    //     r.data  = regs.data;
    //     r.count = regs_top;
    //     log("\n% ==> %\n\n", word, r);
    // }
    if #complete word.type == {
    case .PUSH_INT; {
        if regs_top >= regs.count assert(false, "register stack overflow");
        regs[regs_top] = word.as.push_int;
        regs_top += 1;
        ip += 1;
    }
    case .PUSH_STR; {
        if regs_top >= regs.count-1 assert(false, "register stack overflow");
        // TODO: copy into string storage and escape stuff
        regs[regs_top]   = word.as.push_str.count - 2;
        regs[regs_top+1] = cast,force(int) word.as.push_str.data + 1;
        regs_top += 2;
        ip += 1;
    }
    case .ADD; {
        if regs_top < 2 assert(false, "register stack underflow");
        regs[regs_top-2] = regs[regs_top-2] + regs[regs_top-1];
        regs_top -= 1;
        ip += 1;
    }
    case .GET; {
        if regs_top < 1 assert(false, "register stack underflow");
        // TODO: types, register spreading for larger values
        regs[regs_top-1] = (cast,force(*int) regs[regs_top-1]).*;
        ip += 1;
    }
    case .PUT; assert(false, "TODO: %", word);
    case .GET_VAR; {
        offset, ok := table_find(*bindings, word.as.put_var.name);
        assert(ok);
        regs[regs_top] = cast,force(int) *vars[offset];
        regs_top += 1;
        ip += 1;
    }
    case .PUT_VAR; {
        if regs_top < 1 assert(false, "register stack underflow");
        if vars_top >= vars.count assert(false, "variable stack overflow");
        
        // NOTE: this means that we have shadowing semantics, may be a bad idea
        table_set(*bindings, word.as.put_var.name, vars_top);
        
        // TODO: write a nicer ice
        assert(word.as.put_var.type.count == 1);
        assert(word.as.put_var.type[0].type == .PUSH_TYPE);
        
        (cast(*int)(vars.data+vars_top)).* = regs[regs_top-1];
        vars_top += size_of(int);
        regs_top -= 1;
        ip += 1;
    }
    case .MACRO; {
        old_ip := ip;
        ip = 0;
        while true {
            interpret_word(vm, program, word.as.macro.call.body[ip]);
            if ip <  0 assert(false);
            if ip >= word.as.macro.call.body.count break;
        }
        ip = old_ip+1;
    }
    case .CALL; {
        // log("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!");
        body, ok := table_find(*program.words, word.as.call);
        assert(ok);
        old_ip := ip;
        ip = 0;
        // log("%", body.count);
        // assert(false);
        // TODO: seperate locals
        while true {
            interpret_word(vm, program, body[ip]);
            if ip <  0 assert(false);
            if ip >= body.count break;
        }
        ip = old_ip+1;
    }
    case .PUTC; {
        if regs_top < 1 assert(false, "register stack underflow");
        str: string = ---;
        str.count = 1;
        str.data  = cast(*u8) *regs[regs_top-1];
        write_string(str);
        regs_top -= 1;
        ip += 1;
    }
    case .PUTI; {
        if regs_top < 1 assert(false, "register stack underflow");
        i := regs[regs_top-1];
        print("%", i);
        regs_top -= 1;
        ip += 1;
    }
    case .PUTA; {
        if regs_top < 1 assert(false, "register stack underflow");
        i := regs[regs_top-1];
        print("%", cast,force(*void) i);
        regs_top -= 1;
        ip += 1;
    }
    case .PUTS; {
        if regs_top < 2 assert(false, "register stack underflow");
        str: string = ---;
        str.data  = (cast(**u8)*regs[regs_top-1]).*;
        str.count = regs[regs_top-2];
        regs_top -= 2;
        
        write_string(str);
        ip += 1;
    }
    case .PROC_BEGIN; ip += 1;
    case .PROC_END;   ip += 1;
    case .NAME; assert(false, "TODO: %", word);
    }
}
