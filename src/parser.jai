Procedure :: struct {
    body: []FWord;
    locals: Table(string, []TWord);
}

Block :: struct {
    Tag :: enum {
        PROC;
        MACRO;
        IF;
        WHILE;
    }
    type     : Tag;
    index    : int;
    do_index : int; // additional index used as a label for a do in a while
}

Parser :: struct {
    blocks: [..]Block;
    tape: *[]FWord;
    tape_index: int;
}

match_end :: (blocks: []Block, type: Block.Tag) -> bool {
    if !blocks {
        log_error("unmatched end %", blocks);
        return false;
    }
    if blocks[blocks.count-1].type != type {
        log_error("expected to end %, but ended % instead %", blocks[blocks.count-1], type, blocks);
        return false;
    }
    return true;
}

parse :: (src: string) -> Program, bool {
    words: Table(string, []FWord);
    types: Table(string, []TWord);
    globl: Table(string, []TWord);
    loose: [..]FWord;
    
    using Short_Circuit_Macros(#code { assert(false); return .{}, false; }).{};
    expressions.block_allocator = context.allocator;
    // remember_allocators(*expressions);
    defer release(*expressions);
    
    auto_release_temp();
    parser := Parser.{tape=*loose, blocks.allocator=temp};
    macros := Table(string, Macro).{allocator=temp};
    tokens := Tokenizer.{rhs=src};
    while true {
        expr, eof := parse_expr(*tokens);
        if !expr if eof then break; else Fail();
        defer free_expr(expr);
        if expr.type != .ATOM {
            word, ok := expr_to_word(*parser, expr);
            Check(ok);
            array_add(*loose, word);
            if word.type == .PUT_VAR
            then table_set(*globl, word.as.put_var.name, word.as.put_var.type);
            // log("%", word);
        } else if expr.text == "def" {
            name := parse_expr(*tokens); 
            Check(name != null);
            defer free_expr(name);
            Check(parser.blocks.count == 0, "all word definitions must be in global scope!");
            ws: [..]FWord;
            if #complete name.type == {
            case .ATOM; { // procedure
                array_add(*parser.blocks, .{type=.PROC});
                PushState(parser.tape, *ws);
                PushState(parser.tape_index, 0);
                while true {
                    expr, eof := parse_expr(*tokens);
                    if eof {
                        Check(match_end(parser.blocks, .PROC));
                        parser.blocks.count -= 1;
                        break;
                    }
                    Check(expr != null);
                    defer free_expr(expr);
                    
                    word, ok := expr_to_word(*parser, expr);
                    Check(ok);
                    
                    // REPORT: Short circuit && does not work!?!?!?!??!?!?!?!?
                    // but only when it encounters a PUSH_INT(3) instruction??!?!?!?!?!?
                    if word.type == .NAME if word.as.name == "end" {
                        Check(match_end(parser.blocks, .PROC));
                        parser.blocks.count -= 1;
                        break;
                    }
                    // if word.type == .PROC_END break;
                    if !(word.type == .NAME && !word.as.name) {
                        parser.tape_index += 1;
                        array_add(*ws, word);
                    }
                }
                
                table_add(*words, name.text, ws);
            }
            case .CALL; { // macro
                Check(parser.blocks.count == 0, "all macro definitions must be in global scope!");
                array_add(*parser.blocks, .{type=.MACRO});
                PushState(parser.tape, *ws);
                PushState(parser.tape_index, 0);
                args: [..]string; args.allocator = temp;
                for name.as.call.args {
                    if it.count   != 1
                    || it[0].type != .ATOM        
                    || it[0].as.atom.type != .SYM
                    then Fail("macro args must be a single symbol");
                    array_add(*args, it[0].text);
                }
                while true {
                    word, ok := parse_word(*parser, *tokens);
                    Check(ok);
                    // TODO: parser should have a context stack for blocks and stuff
                    if word.type == .NAME && word.as.name == "end" {
                        Check(match_end(parser.blocks, .MACRO));
                        parser.blocks.count -= 1;
                        break;
                    }
                    // if word.type == .PROC_END break;
                    if !(word.type == .NAME && !word.as.name) {
                        parser.tape_index += 1;
                        array_add(*ws, word);
                    }
                }
                table_set(*macros, name.as.call.head, .{args, ws});
            }
            }
        } else if expr.text == "type" {
            name := parse_expr(*tokens);
            defer free_expr(name);
            assert(name != null);
            if name.type != .ATOM assert(false);
            tws: [..]TWord;
            while true {
                expr := parse_expr(*tokens);
                assert(expr != null);
                defer free_expr(expr);
                if expr.type == .ATOM && expr.text == "end" break;
                tw, ok := expr_to_type(expr);
                assert(ok);
                array_add(*tws, tw);
            }
            table_set(*types, name.text, tws);
        } else {
            word, ok := expr_to_word(*parser, expr);
            Check(ok);
            if !(word.type == .NAME && !word.as.name) {
                parser.tape_index += 1;
                array_add(*loose, word);
            }
            if word.type == .PUT_VAR
            then table_set(*globl, word.as.put_var.name, word.as.put_var.type);
        }
    }
    
    // TODO: really need to start making these errors comprehendable at some point
    Check(parser.blocks.count == 0, "missing % end statements!", parser.blocks.count);
    
    program := Program.{words, types, globl, loose};
    
    // NOTE: for now we do not support nested macros
    for def: macros {
        for * it: def.body if it.type == .NAME {
            if array_find(def.args, it.as.name)     then continue;
            if !resolve_name(*program, null, *macros, it) then Fail();
        }
    }
    
    for * loose if it.type == {
        case .NAME;  if !resolve_name(*program, null, *macros, it) Fail();
        case .MACRO; fill_macro_body(*macros, *it.as.macro.call, it.as.macro.name);
    }
    
    local_scope := Table(string, []TWord).{allocator=temp};
    for body, name: program.words {
        table_reset(*local_scope);
        for * body if it.type == {
        case .PUT_VAR; table_set(*local_scope, it.as.put_var.name, it.as.put_var.type);
        case .NAME;    Check(resolve_name(*program, *local_scope, *macros, it));
        case .MACRO;   fill_macro_body(*macros, *it.as.macro.call, it.as.macro.name);
        }
    }
    
    return program, true;
}

fill_macro_body :: (macros: *Table(string, Macro), m: *Macro, n: string) {
    if !m.body {
        macro, ok := table_find(macros, n);
        assert(ok, "%", n);
        assert(m.args.count == 0, "TODO: macro args");
        m.body = macro.body;
    }
}

resolve_name :: (
    using program : *Program,
    locals        : *Table(string, []TWord),
    macros        : *Table(string, Macro),
    word          : *FWord
) -> bool {
    assert(program != null);
    // locals can be null
    assert(macros != null);
    assert(word != null);
    assert(word.type == .NAME);
    name := word.as.name;
    
    _, ok := table_find(*words, name);
    if ok {
        word.* = .{type=.CALL, as.call=name};
        return true;
    }
    
    if locals {
        ts:, ok = table_find(locals, name);
        if ok {
            word.* = .{type=.GET_VAR, as.get_var=name};
            return true;
        }
    }
    
    ts:, ok = table_find(*globl, name);
    if ok {
        word.* = .{type=.GET_VAR, as.get_var=name};
        return true;
    }
    
    macro:, ok = table_find(macros, name);
    if ok {
        // TODO: ensure arity is 0
        word.* = .{type=.MACRO, as.macro=.{name, macro}};
        return true;
    }
    
    log_error("unkown word %", name);
    return false;
}

expr_to_word :: (parser: *Parser, expr: Expr) -> FWord, bool {
    using Short_Circuit_Macros(#code return .{}, false).{};
    if #complete expr.type == {
    case .ATOM; if #complete expr.as.atom.type == {
        case .ERR; assert(false, "TODO: ERR"); Fail();
        case .EOF; assert(false, "TODO: EOF"); Fail();
        case .SYM; if expr.text == {
            // TODO: context stkack stuff to differentiate different kinds of ends
            case "putc"; return .{type=.PUTC}, true;
            case "putb"; return .{type=.PUTB}, true;
            case "puti"; return .{type=.PUTI}, true;
            case "puts"; return .{type=.PUTS}, true;
            case "puta"; return .{type=.PUTA}, true;
            
            case "rot";  {
                return .{type=.ROT, as.rot=1}, true;
            }
            case "dup";  return .{type=.DUP, as.dup=1}, true;
            case "drop"; return .{type=.DROP, as.dup=1}, true;
            
            case "do"; {
                Check(parser.blocks.count > 0 && parser.blocks[parser.blocks.count-1].type == .WHILE,
                      "'do' can only be used inside a while loop!");
                parser.blocks[parser.blocks.count-1].do_index = parser.tape_index;
                return .{type=.JIF}, true;
            }
            case "if"; {
                array_add(*parser.blocks, .{.IF, parser.tape_index, -1});
                return .{type=.JIF}, true;
            }
            case "while"; {
                array_add(*parser.blocks, .{.WHILE, parser.tape_index, -1});
                return .{type=.NAME}, true;
            }
            case "end";  {
                Check(parser.blocks.count != 0, "unmatched end!");
                b := parser.blocks[parser.blocks.count-1];
                if #complete b.type == {
                case .IF; {
                    assert(parser.tape.*[b.index].type == .JIF);
                    parser.blocks.count -= 1;
                    parser.tape.*[b.index].as.jif = cast(u32) parser.tape_index;
                    // NOTE: sometimes we don't want to add any words to the tape
                    //       so we denote a name statement with no name as a word
                    //       that should not be appended
                    return .{type=.NAME}, true;
                }
                case .WHILE; {
                    assert(parser.tape.*[b.do_index].type == .JIF);
                    parser.blocks.count -= 1;
                    parser.tape.*[b.do_index].as.jif = cast(u32) (parser.tape_index+1);
                    return .{type=.JMP,  as.jmp=cast(u32)b.index}, true;
                }
                case .PROC;  return .{type=.NAME, as.name=expr.text}, true;
                case .MACRO; return .{type=.NAME, as.name=expr.text}, true;
                case; assert(false, "%", b); Fail();
                }
                
            }
            case; return .{type=.NAME, as.name=expr.text}, true;
        }
        case .NUM;    return .{type=.PUSH_INT, as.push_int=expr.as.atom.number}, true;
        case .STR;    return .{type=.PUSH_STR, as.push_str=copy_string(expr.text)}, true;
        case .OP_ADD; return .{type=.ADD}, true;
        case .OP_GET; return .{type=.GET}, true;
        case .OP_PUT; return .{type=.PUT}, true;
        case .OP_GT;  return .{type=.GT},  true;
        case .OP_LT;  return .{type=.LT},  true;
        case .OP_SUB; assert(false, "TODO: OP_SUB"); Fail();
        case .OP_MUL; assert(false, "TODO: OP_MUL"); Fail();
        case .OP_DIV; return .{type=.DIV}, true;
        case .OP_EXP; assert(false, "TODO: OP_EXP"); Fail();
        case .PAREN_OPEN;  assert(false, "TODO: PAREN_OPEN");  Fail();
        case .PAREN_CLOSE; assert(false, "TODO: PAREN_CLOSE"); Fail();
        case; assert(false); Fail();
    }
    case .CALL; using expr.as.call; if head == {
        case "cast"; {
            Check(args.count == 1, "cast expects a single argument! got %", args);
            ts: [..]TWord;
            for args[0] {
                t, ok := expr_to_type(it);
                Check(ok);
                array_add(*ts, t);
            }
            return .{type=.CASTT, as.castt=ts}, true;
        }
        case "var"; {
            tws: [..]TWord;
            if args.count == {
            case 1; {
                Check(args[0].count == 1 && args[0][0].type == .ATOM,
                      "expected single symbol but got %", args);
                array_add(*tws, .{type=.NAME, as.name=""}); // this means infer the type later
            } 
            case 2; {
                Check(args[0].count == 1 && args[0][0].type == .ATOM,
                      "expected single symbol but got %", args);
                for args[1] {
                    tw, ok := expr_to_type(it);
                    Check(ok, cleanup=array_free(tws));
                    array_add(*tws, tw);
                }
            }
            case; Fail("incorrect number of arguments to var operator");
            }
            return .{type=.PUT_VAR, as.put_var=.{args[0][0].text, tws}}, true;
        }
        case "size_of"; {
            Check(args.count == 1, "size_of expects a single argument! got %", args);
            ts: [..]TWord;
            for args[0] {
                tw, ok := expr_to_type(it);
                Check(ok, cleanup=array_free(ts));
                array_add(*ts, tw);
            }
            return .{type=.SIZE_OF_TYPE, as.size_of_type=ts}, true;
        }
        case "dup"; {
            Check(args.count == 1, "dup expects a single argument! got %", args);
            Check(args[0].count == 1, "dup expects a single argument! got %", args);
            a := args[0][0];
            Check(a.type == .ATOM && a.as.atom.type == .NUM, "dup expects a single number, but got %", a);
            n := a.as.atom.number;
            Check(n >= 1, "Expected 1 or greater in dup, but got %", n);
            return .{type=.DUP, as.dup=n}, true;
        }
        case "drop"; {
            Check(args.count == 1, "drop expects a single argument! got %", args);
            Check(args[0].count == 1, "drop expects a single argument! got %", args);
            a := args[0][0];
            Check(a.type == .ATOM && a.as.atom.type == .NUM, "drop expects a single number, but got %", a);
            n := a.as.atom.number;
            Check(n >= 1, "Expected 1 or greater in drop, but got %", n);
            return .{type=.DROP, as.drop=n}, true;
        }
        case; {
            idents: [..]string;
            for args {
                if args.count != 1     assert(false);
                if it[0].type != .ATOM assert(false);
                array_add(*idents, it[0].text);
            }
            return .{type=.MACRO, as.macro=.{head, .{idents, .[]}}}, true;
        }
    }
    case; assert(false); Fail();
    }
    
    assert(false);
    return .{}, false;
}

expr_to_type :: (expr: Expr) -> TWord, bool {
    // log("% ==> %", expr.text, expr);
    if #complete expr.type == {
    case .ATOM; if expr.text == {
        case "int";  return .{type=.PUSH_TYPE, as.push_type=*TYPE_INT}, true;
        case "addr"; return .{type=.PUSH_TYPE, as.push_type=*TYPE_ADR}, true;
        case "ptr";  return .{type=.POINTERIFY}, true;
        case; return .{type=.NAME, as.name=expr.text}, true;
    }
    case .CALL; using expr.as.call; if head == {
        case "name"; {
            if args.count      != 1     assert(false);
            if args[0].count   != 1     assert(false);
            if args[0][0].type != .ATOM assert(false);
            return .{type=.ADD_NAME, as.add_name=args[0][0].text}, true;
        }
        case; assert(false, "%: %", expr.text, expr);
    }
    
    }
    assert(false);
    return .{}, false;
}

parse_word :: (parser: *Parser, tokens: *Tokenizer) -> FWord, bool {
    expr, eof := parse_expr(tokens);
    if !expr {
        if eof log_error("unexpected end of file %", parser.blocks);
        return .{}, false;
    }
    defer free_expr(expr);
    word, ok := expr_to_word(parser, expr);
    if !ok return .{}, false;
    return word, true;
}

parse_type :: (tokens: *Tokenizer) -> TWord, bool {
    expr := parse_expr(tokens);
    if !expr return .{}, false;
    defer free_expr(expr);
    type, ok := expr_to_type(expr);
    if !ok return .{}, false;
    return .{}, false;
}

// parse_expr :: (tokens: *Tokenizer) -> *Expr, eof: bool {
//     e, eof := inline _parse_expr(tokens);
//     if e if eof log("parsed EOF"); else log("parsed %", e.*);
//     return e, eof;
// }
parse_expr :: (tokens: *Tokenizer) -> *Expr, eof: bool {
    expr  :  *Expr;
    token := next(tokens);
    // log("%: %", token.text, token.type);
    // assert(token.text.count != 0);
    
    if is_atom(token.type) || is_op(token.type) expr = make_atom(token);
    else if token.type == {
    case .ERR; return null, false;
    case .EOF; return null, true;
    case; assert(false, "TODO: handle %", token);
    }
    
    token = peek(tokens);
    if token.type == .PAREN_OPEN {
        advance(tokens);
        args: [..]Ast;
        while outer := true {
            arg: [..]*Expr;
            while inner := true {
                t := peek(tokens);
                if t.type == .PAREN_CLOSE {
                    if args.count array_add(*args, arg);
                    token = t;
                    advance(tokens);
                    if arg arg[arg.count-1].repr = join(arg[arg.count-1].repr, token.repr);
                    else expr.repr = join(expr.repr, t.repr);
                    break outer;
                } else if t.type == .SYM && t.text == "," {
                    advance(tokens);
                    break inner;
                }
                
                tokens.peeking = false;
                e := parse_expr(tokens);
                if !e {
                    for ast: args {
                        for ast free_expr(it);
                        array_free(ast);
                    }
                    array_free(args);
                    free_expr(expr);
                    return null, false;
                }
                
                array_add(*arg, e);
                t = peek(tokens);
                if t.type == .PAREN_CLOSE || (t.type == .SYM && t.text == ",") {
                    token = t;
                    advance(tokens);
                    if t.type == .PAREN_CLOSE {
                        e.repr = join(e.repr, token.repr);
                        array_add(*args, arg);
                        break outer; 
                    } else break inner;
                }
                
                tokens.peeking = false;
            }
            array_add(*args, arg);
        }
        
        if token.type != .PAREN_CLOSE {
            log_error("% unmatched parens at %", token.location, expr.location);
            for ast: args {
                for ast free_expr(it);
                array_free(ast);
            }
            array_free(args);
            free_expr(expr);
            return null, false;
        }
        
        expr = make_call(expr, args);
        // eep! this is very janky whoops TODO
        if expr.as.call.args {
            last := expr.as.call.args[expr.as.call.args.count-1];
            last[last.count-1].text.count -= 1;
        } else {
            expr.as.call.head.count -= 2;
        }
    } else {
        tokens.peeking = false;
    }
    
    return expr, false;
}


// TODO: fix Slab_Allocator module and use a Fridge(Expr) instead of making trash constantly
// expressions: Fridge(Expr);
// or maybe all expressions can just be temp allocated since we dont need them after parse?
// but on the other hand, the concatenative-ness of the language means that we only
// ever have a pretty small amount of Exprs in flight at any given moment, meaning we
// can potentially save memory if we were to reuse them instead pooling allocations
// expressions: void;
// i := 0;
expressions: Pool;
get :: (e: *void, $initialize:=true) -> *Expr {
    // i += 1;
    // log("+%", i);
    return New(Expr, initialized=initialize,, Allocator.{pool_allocator_proc, *expressions});
}
del :: (e: *void, expr: *Expr) {
    // i -= 1;
    // log("-%", i);
    free(expr,, Allocator.{pool_allocator_proc, *expressions});
}

// TODO: properly route Rerps throughought the compilation process and output better
//       error messages because they are very stinky and bad right now
Repr :: struct {
    text: string;
    location: Source_Code_Range;
}

join :: (a: Repr, b: Repr) -> Repr {
    using repr: Repr = ---;
    text.data  = a.text.data;
    text.count = (b.text.data + b.text.count) - a.text.data;
    location.fully_pathed_filename  = a.location.fully_pathed_filename;
    location.line_number_start      = a.location.line_number_start;
    location.line_number_end        = b.location.line_number_end;
    location.character_number_start = a.location.character_number_start;
    location.character_number_end   = b.location.character_number_end;
    return repr;
}

Ast  :: []*Expr;
Expr :: struct {
    using data: Tagged(union {
        atom: struct { type: Token_Type; number: int; };
        call: struct { head: string; args: []Ast; };
    });
    using #as repr: Repr;
}

free_expr :: (expr: *Expr) {
    free_children(expr);
    del(*expressions, expr);
}

free_children :: (using expr: *Expr) {
    if #complete type == {
    case .ATOM;
    case .CALL;  using as.call; {
        for ast: args {
            for ast free_expr(it);
            array_free(ast);
        }
        array_free(args);
    }
    }
}

make_atom :: (token: Token) -> *Expr {
    expr := get(*expressions);
    inline init_atom(expr, token);
    return expr;
}

init_atom :: (using expr: *Expr, token: Token) {
    assert(is_atom(token.type) || is_op(token.type),
           "Token `%` (%) is not an atom!", token.text, token.type);
    type = .ATOM;
    text = token.text;
    repr = token.repr;
    as.atom.type = token.type;
    if token.type == .NUM
    then _, as.atom.number = parse_number(token.text, 0);
}

make_call :: (head: Repr, args: []Ast) -> *Expr {
    expr := get(*expressions, initialize=false);
    inline init_call(expr, head, args);
    return expr;
}

init_call :: (expr: *Expr, head: Repr, args: []Ast) {
    assert(xx expr);
    expr.type = .CALL;
    expr.as.call.head = head.text;
    expr.as.call.args = args;
    
    if args {
        last := args[args.count-1];
        assert(last.count > 0);
        expr.repr = join(head, last[last.count-1].repr);
    } else {
        expr.repr = head;
        expr.location.character_number_end += 2;
    }
}

Token_Type :: enum {
    ERR :: 0;
    EOF :: 1;
    
    // atoms
    SYM :: 2;
    NUM :: 3;
    STR :: 4;
    
    // delimeters
    PAREN_OPEN   :: #char "(";
    PAREN_CLOSE  :: #char ")";
    
    // operators
    OP_GET :: #char ".";
    OP_PUT :: #char "!";
    OP_ADD :: #char "+";
    OP_SUB :: #char "-";
    OP_MUL :: #char "*";
    OP_DIV :: #char "/";
    OP_EXP :: #char "^";
    OP_GT  :: #char ">";
    OP_LT  :: #char "<";
}

is_op :: (char: int) -> Token_Type { #insert -> string { // OP_* | ERR
    sb: String_Builder;
    append(*sb, "if cast(Token_Type) char == {\n");
    ti := type_info(Token_Type);
    for ti.names if starts_with(it, "OP_") {
        print_to_builder(*sb, "case .%1; return .%1;\n", it);
    }
    append(*sb, "case; return .ERR;\n}\n");
    str := builder_to_string(*sb);
    // log("%", str);
    return str;
} }

is_op :: (type: Token_Type) -> bool { #insert -> string {
    sb: String_Builder;
    append(*sb, "return ");
    first := true;
    for type_info(Token_Type).names if starts_with(it, "OP_") {
        if first then first = false;
        else append(*sb, " || ");
        print_to_builder(*sb, "type == .%", it);
    }
    append(*sb, ";\n");
    str := builder_to_string(*sb);
    // log("%", str);
    return str;
} }

is_atom :: inline (type: Token_Type) -> bool {
    return type == .NUM || type == .SYM || type == .STR;
}

Token :: struct {
    type: Token_Type = .ERR;
    using #as repr: Repr;
}

Tokenizer :: struct {
    rhs: string; // a sliding view into the source
    cursor: Source_Code_Location;
    
    peeking    : bool;
    peek_token : Token;
    peek_line  : int;
    peek_char  : int;
}

next :: (using tokens: *Tokenizer) -> Token {
    t := ifx peeking then peek_token else inline peek(tokens);
    inline advance(tokens);
    return t;
}

advance :: (using tokens: *Tokenizer) {
    assert(peeking);
    peeking = false;
    
    new_data  := peek_token.text.data + peek_token.text.count;
    delta     := new_data - rhs.data;
    rhs.data   = new_data;
    rhs.count -= delta;
    
    cursor.line_number      = peek_line;
    cursor.character_number = peek_char;
}

peek :: (using tokens: *Tokenizer) -> Token {
    Cursor :: () -> Source_Code_Range #expand { return .{
        cursor.fully_pathed_filename,
        peek_line,
        peek_line,
        peek_char,
        peek_char+1,
    }; }
    assert(!peeking);
    
    peeking   = true;
    peek_line = cursor.line_number;
    peek_char = cursor.character_number;
    
    token: Token;
    token.text = rhs;
    token.type = .EOF;
    if !token.text return .{type = .EOF, location = Cursor()};
    while token.text if token.text[0] == { // TODO: comments
        case #char " "; #through; case #char "\t"; {
            peek_char += 1;
            advance(*token.text);
        }
        case #char "\n"; {
            peek_char  = 0;
            peek_line += 1;
            advance(*token.text);
        }
        case; break;
    }
    if !token.text return .{type = .EOF, location = Cursor()};
    
   
    token.text.count = 1;
    token.location   = Cursor();
    
    Yield :: (type: Token_Type) #expand {
        token.type = type;
        peek_token = token;
        using,except(type) token;
        location.character_number_end = location.character_number_start + text.count;
        `return token;
    }
    
    NotEof :: () -> bool #expand {
        return (token.text.data + token.text.count) < (rhs.data + rhs.count);
    }
    
    if token.text[0] == {
    case #char "("; Yield(.PAREN_OPEN);
    case #char ")"; Yield(.PAREN_CLOSE);
    case #char "\""; while true {
        peek_char        += 1;
        token.text.count += 1;
        if !NotEof() ||  token.text[token.text.count-1] == #char "\n" {
            log_error("unterminated string literal");
            Yield(.ERR);     
        } else if token.text[token.text.count-1] == #char "\"" {
            Yield(.STR);
        }
    }
    }
    
    b := is_op(token.text[0]);
    if b != .ERR Yield(b);
    
    if is_digit(token.text[0]) {
        while NotEof() && is_digit((token.text.data + token.text.count).*) {
            peek_char += 1;
            token.text.count += 1;
        }
        Yield(.NUM);
    }
    
    while NotEof() && (is_alpha((token.text.data + token.text.count).*) || ((token.text.data + token.text.count).* == #char "_")) {
        peek_char += 1;
        token.text.count += 1;
    }
    
    Yield(.SYM);
}