#use "semantic-analyser.ml";;

open Semantics;;
open Tag_Parser;;

let var_free_eq_wrapper v1 v2 = 
    match v1 , v2 with
        |VarFree(vf1) , VarFree(vf2) -> (compare vf1 vf2)==0
        | _ , _ -> false;;

let sexpr_eq_wrapper sexp1 sexp2 =
    match sexp1 , sexp2 with
            |Sexpr(sexp1) , Sexpr(sexp2) -> (sexpr_eq sexp1 sexp2)
            | Void , Void ->true
            | _ , _ -> false;;

let rec retrieve_const_offset c consts = 
        match consts with
            | [] -> -999
            | ((const_sexpr , const_offset) , str)::cdr -> 
                                    begin 
                                        if (sexpr_eq_wrapper c const_sexpr) then const_offset
                                        else (retrieve_const_offset c cdr)
                                    end;; 
                                    
    let rec retrieve_fvar_label v fvars = 
        match fvars with 
            | [] -> -999
            | (var_str , var_offset) :: cdr -> 
                                                    begin
                                                        if((compare var_str v)==0) then var_offset
                                                        else (retrieve_fvar_label v cdr)
                                                    end;;


module type CODE_GEN = sig
  val make_consts_tbl : expr' list -> ((constant * int) * string) list
  val make_fvars_tbl : expr' list -> (string * int) list
  val generate : ((constant * int) * string) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct
        
        let prims_list = ["boolean?" ; "float?"; "integer?"; "pair?"; "null?" ; "char?" ; "vector?" ; "string?" ;
                                "procedure?" ; "symbol?" ; "string-length" ; "string-ref"; "string-set!" ; "make-string" ;
                                "vector-length" ; "vector-ref" ; "vector-set!" ; "make-vector" ; "symbol->string" ; 
                                "char->integer" ; "integer->char" ; "eq?" ; "+"; "*" ; "-" ; "/" ; "<" ; "=" ; "apply" ; 
                                "car" ; "cdr" ; "cons" ;  "set-car!" ; "set-cdr!"];;
        
        let rec zip_with lst1 lst2 = match lst1,lst2 with
                                                | [],_ -> []
                                                | _, []-> []
                                                | (x_head :: x_tail),(y_head :: y_tail) -> (x_head , y_head) :: (zip_with x_tail y_tail);;
                                                
        
        let rec is_member element lst comparator = 
            match lst with 
                | [] -> false
                | car::cdr -> begin
                                        if (comparator car element) then true
                                        else (is_member element cdr comparator)
                                    end;;
        
        let rec list_to_set_helper lst set comparator = 
            match lst with
                | [] -> set
                | car::cdr -> begin 
                                        if(is_member car set comparator) then (list_to_set_helper cdr set comparator)
                                        else (list_to_set_helper cdr (set@[car]) comparator)
                                    end;;
        
        let list_to_set lst comparator =
            (list_to_set_helper lst [] comparator)
    
        let rec extend_const c = 
        match c with
            |Sexpr (Symbol(s)) -> [Sexpr (String(s)) ; c]  
            |Sexpr (Pair(car , cdr)) -> (extend_const (Sexpr(car))) @ (extend_const (Sexpr(cdr))) @ [c]
            |Sexpr (Vector(lst)) -> (List.flatten (List.map (fun(element) -> (extend_const (Sexpr(element)))) lst)) @ [c]  
            | _ -> [c];;
    
    let rec extend_constants_helper lst acc = 
        match lst with
            | [] -> []
            | [const] -> acc @ (extend_const(const))
            | car :: cdr -> (extend_constants_helper cdr (acc @ extend_const(car)));;
            
    let extend_constants lst= 
            (extend_constants_helper lst []);;
    
    let rec collect_sexprs expr = 
            match expr with
                |Const' (Sexpr(sexpr)) -> [Sexpr(sexpr)]
                |Const'(Void) -> []
                | Var' (_v) -> []
                | Box'(_v) -> []
                | BoxGet'(_v) -> []
                | BoxSet'(_v , _expr) -> (collect_sexprs _expr) 
                | If' (test , _then , _else) -> (collect_sexprs test) @ (collect_sexprs _then) @ (collect_sexprs _else)
                | Seq' (_l) -> (List.flatten(List.map collect_sexprs _l))
                | Set' (_var , _val) -> (collect_sexprs _val)
                | Def' (_var , _val) -> (collect_sexprs _val)
                | Or' (_l) ->  (List.flatten (List.map collect_sexprs _l));
                | LambdaSimple' (_vars , _body) -> (collect_sexprs _body)
                | LambdaOpt' (_vars , _opt , _body) -> (collect_sexprs _body)
                | Applic' (_e , _args) -> (collect_sexprs _e) @ (List.flatten (List.map collect_sexprs _args))
                | ApplicTP' (_e , _args) -> (collect_sexprs _e) @ (List.flatten (List.map collect_sexprs _args));;
                    
    let const_size const =
        match const with
            |Void -> 1
            |Sexpr(Nil) -> 1
            |Sexpr (Char(_)) -> 2
            |Sexpr (Bool(_)) -> 2
            |Sexpr (Number(_))-> 9
            |Sexpr (String(str)) -> (String.length str) + 9
            |Sexpr (Symbol(_)) -> 9
            |Sexpr (Vector(lst)) -> (8 * (List.length lst)) + 9
            |Sexpr (Pair(car , cdr)) -> 17;;
    
    let rec get_offsets_helper lst count =
        match lst with
            | [] -> []
            | car :: cdr -> [count] @ (get_offsets_helper cdr (count + (const_size car)))
    
    let get_offsets lst = 
        (get_offsets_helper lst 0)
        
    let rec lookup_offset c consts_offsets = 
        match consts_offsets with
        | [] -> -999
        | (Sexpr(sexp) , offset) :: cdr -> begin 
                                                                if (sexpr_eq sexp c) then offset
                                                                else (lookup_offset c cdr)
                                                            end
        |(Void , _) :: cdr -> (lookup_offset c cdr);;
    
    let my_int_of_char c = 
        (int_of_char c);;
    
    let string_to_ascii_enc str=
        let char_list =  (string_to_list str) in
            List.map my_int_of_char char_list;;
    
    let rec ascii_list_to_string lst acc_str= 
        match lst with 
            | [] -> acc_str
            | [car] -> acc_str ^ (string_of_int car)
            | car :: cdr -> (ascii_list_to_string cdr (acc_str ^ (string_of_int car) ^ " , "));; 
    
    let rec single_const_byte_representation c consts_offsets = 
        match c with
            | Void -> "MAKE_VOID"
            | Sexpr (Nil) -> "MAKE_NIL"
            | Sexpr (Char(ch)) -> "MAKE_LITERAL_CHAR(\'" ^ (Char.escaped ch) ^ "\')"
            | Sexpr (Bool(b)) -> begin 
                                                match b with
                                                    |true -> "MAKE_BOOL(1)"
                                                    |false -> "MAKE_BOOL(0)"
                                            end
            | Sexpr(Number(Int(i))) -> "MAKE_LITERAL_INT(" ^ (string_of_int i) ^ ")"
            | Sexpr(Number(Float(flt))) -> "MAKE_LITERAL_FLOAT(" ^ (string_of_float flt) ^ ")"
            | Sexpr(String(str)) -> "MAKE_LITERAL_STRING " ^ (ascii_list_to_string (string_to_ascii_enc str) "")
            | Sexpr(Symbol(sym)) -> "MAKE_LITERAL_SYMBOL(const_tbl+" ^ (string_of_int (lookup_offset (String(sym)) consts_offsets)) ^ ")"
            | Sexpr(Vector(lst)) -> "MAKE_LITERAL_VECTOR"
            | Sexpr(Pair(car , cdr)) -> "MAKE_LITERAL_PAIR(const_tbl+" ^ (string_of_int (lookup_offset car consts_offsets)) ^ ", const_tbl +" ^(string_of_int (lookup_offset cdr consts_offsets)) ^ ")";;
            
        
         let rec get_byte_representation consts_lst consts_offsets = 
            match consts_lst with
                | [] -> []
                | car :: cdr -> [(single_const_byte_representation car consts_offsets)] @ (get_byte_representation cdr consts_offsets);;
                
    let populate_table lst = 
        let offsets = (get_offsets lst) in
            let consts_offsets = (zip_with lst offsets) in
                let byte_representation = (get_byte_representation lst consts_offsets) in
                        (zip_with consts_offsets byte_representation);;
                        
         let make_consts_tbl asts = 
            (populate_table (list_to_set (extend_constants (list_to_set ([Void ; Sexpr (Nil) ; Sexpr (Bool (false)) ; Sexpr (Bool (true))] @ (List.flatten (List.map collect_sexprs asts))) sexpr_eq_wrapper )) sexpr_eq_wrapper ));;
            
    let rec collect_fvars expr = 
        match expr with
                |Const' (Sexpr(sexpr)) -> []
                |Const'(Void) -> []
                | Var'(VarFree(v)) -> [VarFree(v)]
                | Var' (_) -> []
                | Box'(_) -> []
                | BoxGet'(_) -> []
                | BoxSet'(_v , _expr) -> (collect_fvars _expr) 
                | If' (test , _then , _else) -> (collect_fvars test) @ (collect_fvars _then) @ (collect_fvars _else)
                | Seq' (_l) -> (List.flatten (List.map collect_fvars _l))
                | Set' (_var , _val) -> (collect_fvars _var) @ (collect_fvars _val)
                | Def' (_var , _val) -> (collect_fvars _var) @ (collect_fvars _val)
                | Or' (_l) ->  (List.flatten (List.map collect_fvars _l));
                | LambdaSimple' (_vars , _body) -> (collect_fvars _body)
                | LambdaOpt' (_vars , _opt , _body) -> (collect_fvars _body)
                | Applic' (_e , _args) -> (collect_fvars _e) @ (List.flatten (List.map collect_fvars _args))
                | ApplicTP' (_e , _args) -> (collect_fvars _e) @ (List.flatten (List.map collect_fvars _args));;
    
    let rec add_fvars_index_helper lst count = 
        match lst with
            | [] -> []
            |VarFree(v) :: cdr -> [(v , count)] @ (add_fvars_index_helper cdr (count+8))
            | _ :: cdr -> (add_fvars_index_helper cdr count);;
    
    let add_fvars_index lst = 
        (add_fvars_index_helper lst 0);;
    
    let string_lst_to_var_free_lst str = VarFree (str);;
    
    let make_fvars_tbl asts = (add_fvars_index (list_to_set ((List.map string_lst_to_var_free_lst prims_list) @ (List.flatten (List.map collect_fvars asts))) var_free_eq_wrapper ));;
    
    let or_counter = ref 0;;
   
    let if_counter = ref 0;;
                                                    
    let increment_counter counter= counter := !counter +1;;

    let generate_lambda_s params generated_body = 
        (Printf.sprintf
    "
    ;get pointer to prev_env:
    mov rax, [rbp + WORD_SIZE * 2]

    ;check for type of env: 
    ;the length of the env will be in rbx

    cmp rax, T_VECTOR

    jne .L_undefined:

        .L_vector:
            VECTOR_LENGTH rbx rax
            inc rbx

            ;creating the lambda env:
            mov rdx, qword [rbp + 3 * WORD_SIZE] ;holds the number of params

            ;allocating and setting a vector to hold the params_env:
            lea rdi, [rdx * WORD_SIZE + WORD_SIZE + TYPE_SIZE] 
            MALLOC rdi, rdi ;holds the allocated memory for the new env
            mov byte [rdi], T_VECTOR
            mov qword [rdi+TYPE_SIZE], rdx
            add rdi, WORD_SIZE+TYPE_SIZE

            mov r10, qword [rbp + 3 * WORD_SIZE] ;num of arguments
            mov r9, qword [rbp + 4 * WORD_SIZE] ; first arguement

            jmp .L_len_exit

        .L_undefined:
            mov rbx, 1 
            mov rdx, 0
            ;allocating and setting a vector to hold the params_env:
            lea rdi, [rdx * WORD_SIZE + WORD_SIZE + TYPE_SIZE] 
            MALLOC rdi, rdi ;holds the allocated memory for the new env
            mov byte [rdi], T_VECTOR
            mov qword [rdi+TYPE_SIZE], rdx
            add rdi, WORD_SIZE+TYPE_SIZE
            mov r10, 0
               

    .L_len_exit:

    push rcx
    mov rcx, 0


    .insert_params_loop:
        cmp rcx, r10
        jz insert_params_loop_exit
        mov r11, qword [r9 + rcx*WORD_SIZE]
        mov qword [rdi+rcx*WORD_SIZE], r11
        inc rcx
        jmp .insert_params_loop

    .insert_params_loop_exit:

    pop rcx

    ;allocating and setting a vector to hold the external_env:
    lea rsi, [rbx * WORD_SIZE + WORD_SIZE + TYPE_SIZE]
    MALLOC rsi, rsi
    mov byte [rsi], T_VECTOR
    mov qword [rsi+TYPE_SIZE], rbx

    add rsi, WORD_SIZE + TYPE_SIZE
    ; rcx - i, r9 - j 

    push rcx 

    mov rcx, 0
    mov r9, 1
    dec rbx

    .insert_data_loop:
    cmp rcx, rbx
    je .insert_data_loop_exit

        ;ExtEnv[r9] = Env[rcx]
        mov r8, qword [rax + rcx * WORD_SIZE]
        mov qword [rsi + r9*WORD_SIZE], r8

        inc rcx
        inc r9

    jmp .insert_data_loop

    .insert_data_loop_exit :

    pop rcx
    inc rbx

    mov qword [rsi], rdi
    sub rsi, TYPE_SIZE + WORD_SIZE

    MAKE_CLOSURE(rax, rsi, Lcode)

    jmp Lcont

    Lcode: 
    push rbp 
    mov rbp, rsp
    %s
    leave 
    ret

    Lcont:
    " 
    generated_body) ;;




    let generate consts fvars e = 
            let rec gen expr = 
                match expr with
                    | Const' (c) -> "mov rax, const_tbl + " ^ (string_of_int (retrieve_const_offset c consts))
                    
                    | Var' (VarParam (_ , minor)) -> "mov rax , qword [rbp + 8 * (4 + "^(string_of_int minor)^" )]"
                    
                    | Var'(VarBound (_ , major , minor)) -> "mov rax , qword [rbp + 8 * 2] \n " ^
                                                                                "mov rax , qword [rax + 8 * " ^ (string_of_int major) ^" ]\n" ^
                                                                                "mov rax , qword [rax + 8 * " ^ (string_of_int minor) ^ " ]"
                                                                                
                    | Var' (VarFree (v)) -> "mov rax , qword [fvar_tbl + " ^ (string_of_int (retrieve_fvar_label v fvars)) ^ " ]"
                    
                    | Set' (Var'(VarParam (_ , minor)) , _val) -> (gen _val) ^ "\n" ^
                                                                                        "mov qword [rbp + 8 * (4 + "^ (string_of_int minor) ^ " )] , rax\n" ^
                                                                                        "mov rax , SOB_VOID_ADDRESS"
                                                                                        
                    | Set'(Var' (VarBound (_ , major , minor)) , _val) -> (gen _val) ^ "\n" ^
                                                                                                    "mov rbx , qword [rbp + 8 * 2]\n" ^
                                                                                                    "mov rbx , qword [rbx + 8 * " ^ (string_of_int major) ^ " ]\n" ^
                                                                                                    "mov qword [rbx + 8 * " ^ (string_of_int minor) ^ " ]\n" ^
                                                                                                    "mov rax , SOB_VOID_ADDRESS"
                                                                                                    
                    | Set'(Var'(VarFree (v)) , _val) -> (gen _val) ^ "\n" ^
                                                                        "mov qword [ fvar_tbl + " ^ (string_of_int (retrieve_fvar_label v fvars)) ^ " ] , rax\n" ^
                                                                        "mov rax , SOB_VOID_ADDRESS"
                                                                        
                    |Seq'(_l) ->  let rec gen_seq lst str = 
                                            match lst with
                                                | [] -> str
                                                | car :: cdr -> (gen_seq cdr (str ^ (gen car) ^ "\n")) 
                                        in (gen_seq _l "") 
                                        
                    | Or' (_l) -> (increment_counter or_counter) ;
                                        let rec gen_or lst str = 
                                            match lst with
                                                | [] -> str
                                                | [car] -> str ^ (gen car) ^ "\nLexit"  ^ (string_of_int !or_counter) ^ ": \n"
                                                | car :: cdr -> (gen_or cdr (str ^ (gen car) ^ "\n" ^
                                                                                        "cmp rax , SOB_FALSE_ADDRESS \n" ^
                                                                                        "jne Lexit" ^(string_of_int !or_counter) ^ "\n"))
                                        in (gen_or _l "")
                                        
                    | If'(test , _then , _else) -> (increment_counter if_counter) ; 
                                                            (gen test) ^ "\n" ^
                                                            "cmp rax , SOB_FALSE_ADDRESS \n" ^
                                                            "je Lelse" ^ (string_of_int !if_counter) ^ "\n" ^
                                                            (gen _then) ^ "\n" ^
                                                            "jmp Lexit" ^ (string_of_int !if_counter) ^ "\n" ^
                                                            "Lelse" ^ (string_of_int !if_counter) ^ ": \n" ^
                                                            (gen _else) ^ "\n" ^
                                                            "Lexit" ^ (string_of_int !if_counter) ^ ": \n"


                    | LambdaSimple'(params, body) -> let generated_body = gen body in (generate_lambda_s params generated_body)

                                                            
                    | BoxGet' (v) -> (gen (Var'(v))) ^ "\n" ^
                                            "mov rax , qword [rax]"
                                            
                    | BoxSet'(v , box_set_expr) -> (gen box_set_expr) ^ "\n" ^
                                                                    "push rax \n" ^ 
                                                                    (gen (Var'(v))) ^ "\n" ^
                                                                    "pop qword [rax] \n" ^
                                                                    "mov rax , SOB_VOID_ADDRESS"
                                                                    
                    | Box'(v) -> (gen (Var'(v))) ^ "\n" ^
                                    "push rdx \n" ^
                                    "MALLOC rdx , WORD_SIZE \n" ^
                                    "mov [rdx] , rax \n"^
                                    "mov rax , rdx \n" ^
                                    "pop rdx"
                    
                    | Def' (Var' (VarFree(v)) , _val) -> (gen _val) ^ "\n" ^
                                                                        "mov qword [ fvar_tbl + " ^ (string_of_int (retrieve_fvar_label v fvars)) ^ " ] , rax \n" ^
                                                                        "mov rax , SOB_VOID_ADDRESS"
                                                                        
                    | Applic'(_e , _args) -> (applic_gen _e _args)
                    
                    | ApplicTP' (_e , _args) -> (applic_tp_gen _e _args)
                    
        and applic_gen _e _args = 
            let folder element acc = (acc ^ (gen element)^ "\n" ^ "push rax \n") in
                let push_args_str = (List.fold_right folder _args "") in
                    push_args_str ^ "push " ^ (string_of_int (List.length _args)) ^ "\n" ^
                    (gen _e) ^ "\n" ^
                    "push qword [rax + TYPE_SIZE] \n" ^
                    "call qword [rax + TYPE_SIZE + WORD_SIZE] \n" ^
                    "add rsp , 8 * 1 \n" ^
                    "pop rbx \n" ^
                    "shl rbx , 3 \n" ^
                    "add rsp , rbx \n"
                    
        and applic_tp_gen _e _args = 
            let folder element acc = (acc ^ (gen element) ^ "\n" ^ "push rax \n") in
                let push_args_str = (List.fold_right folder _args "") in
                    push_args_str ^ "push " ^ (string_of_int (List.length _args)) ^ "\n" ^
                    "push qword [rax + TYPE_SIZE] \n" ^
                    "push qword [rbp + WORD_SIZE] \n" ^
                    
                    "push rax \n"^
                    "mov rax , PARAM_COUNT \n" ^
                    "add rax , 4 \n" ^
                    "push rcx \n" ^
                    "mov rcx , 0 \n" ^
                    "applic_tp_loop" ^ (*applic_tp_counter ^*) ": \n" ^
                    "inc rcx \n" ^
                    "dec rax \n" ^
                    "push rax \n" ^
                    "mov rax , WORD_SIZE \n" ^
                    "mov rbx , rbp \n"^
                    "mul rcx \n" ^
                    "sub rbx , rax \n" ^
                    "pop rax \n" ^
                    "mov rbx , [rbx] \n" ^
                    "mov [rbp + WORD_SIZE * rax] , rbx" ^
                    "cmp rcx , " ^ (string_of_int ((List.length _args) + 3)) ^ "\n" ^
                    "jne applic_tp_loop" ^ (*applic_tp_counter ^*) "\n" ^
                    ""
                    
        in
        gen e;;
        
  
  (********************************** functions for printing - delete these *************************************)
  
   let rec print_sexpr = fun sexprObj ->
  match sexprObj  with
    | Bool(true) -> "Bool(true)"
    | Bool(false) -> "Bool(false)"
    | Nil -> "Nil"
    | Number(Int(e)) -> Printf.sprintf "Number(Int(%d))" e
    | Number(Float(e)) -> Printf.sprintf "Number(Float(%f))" e
    | Char(e) -> Printf.sprintf "Char(%c)" e
    | String(e) -> Printf.sprintf "String(\"%s\")" e
    | Symbol(e) -> Printf.sprintf "Symbol(\"%s\")" e
    | Pair(e,s) -> Printf.sprintf "Pair(%s,%s)" (print_sexpr e) (print_sexpr s) 
    | Vector(list)-> Printf.sprintf "Vector(%s)" (print_sexprs_as_list list)

and print_const = fun const ->
  match const with
    | Void -> "Void"
    | Sexpr(s) -> print_sexpr s

and print_sexprs = fun sexprList -> 
  match sexprList with
    | [] -> ""
    | head :: tail -> (print_sexpr head) ^ "," ^ (print_sexprs tail)

and print_consts = fun constsList -> 
  match constsList with
    | [] -> ""
    | head :: tail -> (print_const head) ^ "," ^ (print_consts tail)

and print_sexprs_as_list = fun sexprList ->
  let sexprsString = print_sexprs sexprList in
    "[ " ^ sexprsString ^ " ]"

and print_consts_as_list = fun constsList ->
  let constString = print_consts constsList in
    "[ " ^ constString ^ " ]"

and print_vars = fun varList ->
	match varList with
	| [] -> ""
	| head:: tail -> (print_var head) ^ ", " ^ (print_vars tail)

and print_varfree_as_list = fun varfreeList ->
  let varString = print_vars varfreeList in
    "[ " ^ varString ^ " ]"

and print_expr = fun exprObj ->
  match exprObj  with
    | Const'(Void) -> "Const(Void)"
    | Const'(Sexpr(x)) -> Printf.sprintf "Const(Sexpr(%s))" (print_sexpr x)
    | Var'(VarParam(x, indx)) -> Printf.sprintf "VarParam(\"%s\", %d)" x indx
    | Var'(VarBound(x, indx, level)) -> Printf.sprintf "VarBound(\"%s\" %d %d)" x indx level
    | Var'(VarFree(x)) -> Printf.sprintf "VarFree(\"%s\" )" x
    | If'(test,dit,dif) -> Printf.sprintf "If(%s,%s,%s)" (print_expr test) (print_expr dit) (print_expr dif)
    | Seq'(ls) -> Printf.sprintf "Seq(%s)" (print_exprs_as_list ls)
    | Set'(var,value) -> Printf.sprintf "Set(%s,%s)" (print_expr var) (print_expr value)
    | Def'(var,value) -> Printf.sprintf "Def(%s,%s)" (print_expr var) (print_expr value)
    | Or'(ls) -> Printf.sprintf "Or(%s)" (print_exprs_as_list ls)
    | LambdaSimple'(args,body) -> Printf.sprintf "LambdaSimple(%s,%s)" (print_strings_as_list args) (print_expr body)
    | LambdaOpt'(args,option_arg,body) -> Printf.sprintf "LambdaOpt(%s,%s,%s)" (print_strings_as_list args) option_arg (print_expr body)
    | Applic'(proc,params) -> Printf.sprintf "Applic(%s,%s)" (print_expr proc) (print_exprs_as_list params) 
    | ApplicTP'(proc,params) -> Printf.sprintf "ApplicTP(%s,%s)" (print_expr proc) (print_exprs_as_list params) 
    | Box'(variable) -> Printf.sprintf "Box'(\"%s\" )" (print_var variable)
    | BoxGet'(variable) -> Printf.sprintf "BoxGet'(\"%s\" )" (print_var variable)
    | BoxSet'(variable, expr) -> Printf.sprintf "BoxSet'(\"%s\", %s )" (print_var variable) (print_expr expr)

and print_var = fun x ->
	match x with
	| VarFree(str) -> Printf.sprintf "VarFree(%s)" str
	| VarParam(str, int1) -> Printf.sprintf "VarParam(%s)" str
	| VarBound(str, int1, int2) -> Printf.sprintf "VarBound(%s)" str
and 

print_exprs = fun exprList -> 
  match exprList with
    | [] -> ""
    | head :: [] -> (print_expr head) 
    | head :: tail -> (print_expr head) ^ "; " ^ (print_exprs tail)

and print_exprs_as_list = fun exprList ->
  let exprsString = print_exprs exprList in
    "[ " ^ exprsString ^ " ]"

and print_strings = fun stringList -> 
  match stringList with
    | [] -> ""
    | head :: [] -> head 
    | head :: tail -> head ^ "; " ^ (print_strings tail)

and print_strings_as_list = fun stringList ->
  let stringList = print_strings stringList in
    "[ " ^ stringList ^ " ]";;

let rec printThreesomesList lst =
  match lst with
    | [] -> ()
    | ((name, index), str)::cdr -> print_string (print_const name); print_string " , "; print_int index ; print_string (" "^str^" \n"); printThreesomesList cdr;;
    
   (* let bgbg = run_semantics (tag_parse_expression(Reader.read_sexpr("
    (+ 5 6)
    ")));;
    
    (print_string (generate (make_consts_tbl [bgbg]) (make_fvars_tbl [bgbg]) (bgbg)));; *)

end;;


