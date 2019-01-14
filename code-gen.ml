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
            
    let rec create_vector_offsets_string consts_offsets lst acc_str = 
        match lst with
        | [] -> acc_str
        | [car] -> acc_str ^ ("const_tbl + " ^ (string_of_int (lookup_offset car consts_offsets)))
        | car :: cdr -> (create_vector_offsets_string consts_offsets cdr (acc_str ^ " const_tbl + " ^(string_of_int (lookup_offset car consts_offsets) ^ " , ")));;
    
    let rec single_const_byte_representation c consts_offsets = 
        match c with
            | Void -> "MAKE_VOID"
            | Sexpr (Nil) -> "MAKE_NIL"
            | Sexpr (Char(ch)) -> "MAKE_LITERAL_CHAR(" ^ (string_of_int (int_of_char ch)) ^ ")"
            | Sexpr (Bool(b)) -> begin 
                                                match b with
                                                    |true -> "MAKE_BOOL(1)"
                                                    |false -> "MAKE_BOOL(0)"
                                            end
            | Sexpr(Number(Int(i))) -> "MAKE_LITERAL_INT(" ^ (string_of_int i) ^ ")"
            | Sexpr(Number(Float(flt))) -> "MAKE_LITERAL_FLOAT(" ^ (string_of_float flt) ^ ")" 
            | Sexpr(String(str)) -> "MAKE_LITERAL_STRING " ^ (ascii_list_to_string (string_to_ascii_enc str) "")
            | Sexpr(Symbol(sym)) -> "MAKE_LITERAL_SYMBOL(const_tbl+" ^ (string_of_int (lookup_offset (String(sym)) consts_offsets)) ^ ")"
            | Sexpr(Vector(lst)) -> "MAKE_LITERAL_VECTOR " ^ (create_vector_offsets_string consts_offsets lst "")
            | Sexpr(Pair(car , cdr)) -> "MAKE_LITERAL_PAIR(const_tbl+" ^ (string_of_int (lookup_offset car consts_offsets)) ^ ", const_tbl + " ^(string_of_int (lookup_offset cdr consts_offsets)) ^ ")";;
            
        
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
    
    let applic_tp_counter = ref 0;;

    let lambda_counter = ref 0;;
                                                    
    let increment_counter counter= counter := !counter +1;;

    let is_base_env l_counter= 
    Printf.sprintf
    "
    ;get pointer to prev_env:
    mov rax, [rbp + WORD_SIZE * 2]

    ; creating ExtEnv[0]:
    ;the length of the env will be in rbx

    mov r15, [rax]

    cmp r15, T_UNDEFINED

    je .L_undefined_%d

    " l_counter;;

    let base_env = 
    Printf.sprintf
    "
    mov rbx, 1 ; 1 + |Env|
    mov rdx, 0 ; there are no bound variables 
    lea rdi, [rdx * WORD_SIZE + WORD_SIZE + TYPE_SIZE] 
    MALLOC rdi, rdi ;holds the allocated memory for the new env
    mov byte [rdi], T_VECTOR
    mov qword [rdi+TYPE_SIZE], rdx
    add rdi, WORD_SIZE+TYPE_SIZE
    ";;

    let ext_env l_counter= 
    Printf.sprintf
    "
    VECTOR_LENGTH rbx, rax
    inc rbx ; 1 + |Env|

    ;holds the number of params
    mov rdx, qword [rbp + 3 * WORD_SIZE] 

    ;allocating and setting a vector to hold the params_env:
    lea rdi, [rdx * WORD_SIZE + WORD_SIZE + TYPE_SIZE] 
    MALLOC rdi, rdi ;holds the allocated memory for the new env
    mov byte [rdi], T_VECTOR
    mov qword [rdi+TYPE_SIZE], rdx
    add rdi, WORD_SIZE+TYPE_SIZE

    jmp .setting_params_%d
    " l_counter;;

    let copy_params l_counter= 
    Printf.sprintf
    "
    push rcx
    mov rcx, 0
    lea r9 , [rbp + 4*WORD_SIZE]
    ;ExtEnv[0][i] = param[i]
    .insert_params_loop_%d:
        cmp rcx, rdx
        je .insert_params_loop_exit_%d
        mov r11, qword [r9 + rcx*WORD_SIZE]
        mov qword [rdi+rcx*WORD_SIZE], r11
        inc rcx
        jmp .insert_params_loop_%d

    .insert_params_loop_exit_%d:

    pop rcx

    "l_counter l_counter l_counter l_counter;;

    let copy_to_ext_env l_counter= 
    Printf.sprintf
    "
    ;allocating and setting a vector to hold the ExtEnv:
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

    ;ExtEnv[i+1] = Env[i]
    .insert_data_loop_%d:
        cmp rcx, rbx
        je .insert_data_loop_exit_%d

        ;ExtEnv[r9] = Env[rcx]

        lea r15, [WORD_SIZE + TYPE_SIZE + rcx*WORD_SIZE]
        add r15, rax 
        mov r8, qword [r15] ;to get to the data of the vector who represents the last Env
        mov qword [rsi + r9*WORD_SIZE], r8

        inc rcx
        inc r9

        jmp .insert_data_loop_%d
    "
    l_counter l_counter l_counter;;



    let generate_lambda params generated_body stack_adjustment_value l_counter = 
    increment_counter lambda_counter;
     let lambda_code_gen = (Printf.sprintf
    "
    gen_lambda_%d:
    ;is_base_env:
        %s

        .L_vector%d:
            %s

        .L_undefined_%d:
            %s
               

    .setting_params_%d:
    %s

    ;allocating and setting ExtEnv:
    %s

    .insert_data_loop_exit_%d:

    pop rcx

    ;rdi was pointing on the vectors data
    sub rdi, TYPE_SIZE + WORD_SIZE

    mov qword [rsi], rdi
    sub rsi, TYPE_SIZE + WORD_SIZE

    MAKE_CLOSURE(rax, rsi, Lcode_%d)

    jmp Lcont_%d

    Lcode_%d: 
    push rbp 
    mov rbp, rsp
    %s
    %s
    leave 
    ret

    Lcont_%d:
    " 
    l_counter (is_base_env l_counter) l_counter (ext_env l_counter) l_counter base_env l_counter (copy_params l_counter) 
        (copy_to_ext_env l_counter) l_counter l_counter l_counter l_counter stack_adjustment_value generated_body l_counter) 
    in lambda_code_gen;;

    (*rdx holds (num_of_tot_params - num_of_fixed_params) which means rdx == 0 ? enlarge : shrink*)
    let is_shrink_stack num_of_fixed_params = 
    Printf.sprintf 
    "
    ;rdi - num_of_fixed_params
    mov rdi, %d 

    ;rdx - arg count 
    mov rdx, qword [rbp + 3*WORD_SIZE]

    sub rdx, rdi
    " num_of_fixed_params ;;

    let shrink_stack  num_of_fixed_params lambda_counter= 
    Printf.sprintf
    "
    ;r10 - holds number of fixed params
    mov r10, %d

    ; rdi - holds number of opt params
    mov rdi, [rbp + 3*WORD_SIZE] ;num_of_tot_params
    sub rdi, r10

    
    ;rbx - holds the list
    mov rbx, SOB_NIL_ADDRESS


    lea rsi, [rdi + r10 + 3]
    mov rcx, rdi

    .create_opt_param_list_loop_%d:

        cmp rcx, 0
        je .create_opt_param_list_loop_end_%d
        mov r15, [rbp + rsi*WORD_SIZE] ; r10 - to skip the fixed params; 3 - to skip ret env arg-count ;rcx - the offset of the opt params
        MAKE_PAIR(rax, r15, rbx)
        mov rbx, rax
        dec rsi
        dec rcx
        jmp .create_opt_param_list_loop_%d

    .create_opt_param_list_loop_end_%d:

    ;rsi - holds the offset of the last opt relativly to rbp
    lea rsi, [rdi + r10 + 3]

    ;the last opt is overridden with the list of opts
    mov qword [rbp+rsi*WORD_SIZE], rbx

    
    ;rcx - holds the offset of the last fixed param
    lea rcx, [r10 + 4]

    ;rdi - num_of_opt_params -1
    dec rdi 
    lea rdx, [rcx -1]
    .shift_shrink_loop_%d: 
        cmp rcx, 0
        jz .shift_shrink_loop_end_%d

        ;r9 - PARAMi - top down 
        mov r9, qword [rbp + WORD_SIZE*rdx]
        lea rsi, [rdi + rdx]
        shl rsi, 3
        mov qword [rbp + rsi], r9

        dec rdx
        dec rcx
        jmp .shift_shrink_loop_%d
    
    .shift_shrink_loop_end_%d: 

    ;rdi = rdi * 8
    shl rdi, 3

    add rsp, rdi
    add rbp, rdi

    jmp .update_arg_count_%d

    "   num_of_fixed_params lambda_counter lambda_counter lambda_counter lambda_counter
        lambda_counter lambda_counter lambda_counter lambda_counter lambda_counter;;

    let enlarge_stack num_of_fixed_params lambda_counter= 
    Printf.sprintf
    "
    mov r8 ,4 + %d ; size of frame in bytes
    mov rcx, 0

    .shift_enlarge_loop_%d:
        cmp rcx, r8
        je .shift_enlarge_loop_end_%d

        lea r10, [rbp + rcx * WORD_SIZE]; holds the address of the current param to shift

        mov r9, qword [r10]
        mov [r10 - WORD_SIZE], r9

        inc rcx
    jmp .shift_enlarge_loop_%d

    .shift_enlarge_loop_end_%d:

    ;update pointers to stack:
    sub rsp, WORD_SIZE
    sub rbp, WORD_SIZE

    ;STACK[top] = SOB_NIL_ADDRESS
    ;bottom_frame+size_of_frame = top_frame AKA the last arguement
    mov r12, SOB_NIL_ADDRESS
    ;WORD_SIZE*([rbp 3*WORD_SIZE] + 4)
    mov r10, [rbp + 3*WORD_SIZE]
    add r10, + 4 ; offset to last the opt
    mov [rbp + r10*WORD_SIZE], r12
    " num_of_fixed_params lambda_counter lambda_counter lambda_counter lambda_counter
    ;;

    let update_arg_count num_of_fixed_params = 
    Printf.sprintf
    "
    mov rdi, %d
    inc rdi
    mov qword [rbp + 3*WORD_SIZE], rdi
    "
    num_of_fixed_params;;

    let stack_adjustment fixed_params lambda_counter= 
        let num_of_fixed_params = List.length fixed_params in
        Printf.sprintf 
    "
    adjust_stack_%d:
    %s

    cmp rdx, 0
    je .enlarge_stack_%d

    .shrink_stack_%d:
    %s

    .enlarge_stack_%d:
    %s

    .update_arg_count_%d:
    %s


    "lambda_counter (is_shrink_stack num_of_fixed_params) lambda_counter lambda_counter (shrink_stack num_of_fixed_params lambda_counter) lambda_counter 
    (enlarge_stack num_of_fixed_params lambda_counter) lambda_counter (update_arg_count num_of_fixed_params) ;;




    let generate consts fvars e = 
            let rec gen expr = 
                match expr with
                    | Const' (c) -> "mov rax, const_tbl + " ^ (string_of_int (retrieve_const_offset c consts))
                    
                    | Var' (VarParam (_ , minor)) -> "mov rax , qword [rbp + 8 * (4 + "^(string_of_int minor)^" )]"
                    
                    | Var'(VarBound (_ , major , minor)) -> "mov rax , qword [rbp + 8 * 2] \n " ^
                                                                                "mov rax , qword [TYPE_SIZE + WORD_SIZE + rax + 8 * " ^ (string_of_int major) ^" ]\n" ^
                                                                                "mov rax, [TYPE_SIZE + WORD_SIZE + rax + 8 * " ^ (string_of_int minor) ^ " ]\n" 
                                                                                
                    | Var' (VarFree (v)) -> "mov rax , qword [fvar_tbl + " ^ (string_of_int (retrieve_fvar_label v fvars)) ^ " ]"
                    
                    | Set' (Var'(VarParam (_ , minor)) , _val) -> (gen _val) ^ "\n" ^
                                                                                        "mov qword [rbp + 8 * (4 + "^ (string_of_int minor) ^ " )] , rax\n" ^
                                                                                        "mov rax , SOB_VOID_ADDRESS"
                                                                                        
                    | Set'(Var' (VarBound (_ , major , minor)) , _val) -> (gen _val) ^ "\n" ^
                                                                                                    "mov rbx , qword [rbp + 8 * 2]\n" ^
                                                                                                    "mov rbx , qword [TYPE_SIZE + WORD_SIZE + rbx + 8 * " ^ (string_of_int major) ^ " ]\n" ^
                                                                                                    "mov qword [TYPE_SIZE + WORD_SIZE + rbx + 8 * " ^ (string_of_int minor) ^ " ], rax\n" ^
                                                                                                    "mov rax , SOB_VOID_ADDRESS"
                                                                                                    
                    | Set'(Var'(VarFree (v)) , _val) -> (gen _val) ^ "\n" ^
                                                                        "mov qword [ fvar_tbl + " ^ (string_of_int (retrieve_fvar_label v fvars)) ^ " ] , rax\n" ^
                                                                        "mov rax , SOB_VOID_ADDRESS"
                                                                        
                    |Seq'(_l) ->  let rec gen_seq lst str = 
                                            match lst with
                                                | [] -> str
                                                | car :: cdr -> (gen_seq cdr (str ^ (gen car) ^ "\n")) 
                                        in (gen_seq _l "") 
                                        
                    | Or' (_l) -> let or_exit_label = "or_Lexit"  ^ (string_of_int !or_counter) in
                                        (increment_counter or_counter) ;
                                        let rec gen_or lst str = 
                                            match lst with
                                                | [] -> str
                                                | [car] -> str ^ (gen car) ^ "\n" ^ or_exit_label ^ ": \n"
                                                | car :: cdr -> (gen_or cdr (str ^ (gen car) ^ "\n" ^
                                                                                        "cmp rax , SOB_FALSE_ADDRESS \n" ^
                                                                                        "jne " ^ or_exit_label^ "\n"))
                                        in (gen_or _l "")
                                        
                    | If'(test , _then , _else) -> let if_exit_label = "if_Lexit" ^ (string_of_int !if_counter) in
                                                            let if_else_label = "Lelsle" ^ (string_of_int !if_counter) in
                                                            (increment_counter if_counter) ; 
                                                            (gen test) ^ "\n" ^
                                                            "cmp rax , SOB_FALSE_ADDRESS \n" ^
                                                            "je " ^ if_else_label ^ "\n" ^
                                                            (gen _then) ^ "\n" ^
                                                            "jmp "^ if_exit_label ^"\n" ^
                                                            if_else_label ^ ": \n" ^
                                                            (gen _else) ^ "\n" ^
                                                            if_exit_label^ ": \n"



                    |LambdaSimple'(params, body) -> let generated_body = gen body in 
                                                        (generate_lambda params generated_body "" !lambda_counter)

                    |LambdaOpt'(params, opt, body) -> let generated_body = gen body in 
                                                            (generate_lambda params generated_body (stack_adjustment params !lambda_counter) !lambda_counter)

                                                            
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
                                                                        
                    | Applic'(_e , _args) -> let folder element acc = (acc ^ (gen element)^ "\n" ^ "push rax \n") in
                                                let push_args_str = (List.fold_right folder _args "") in
                                                push_args_str ^ "push " ^ (string_of_int (List.length _args)) ^ "\n" ^
                                                (gen _e) ^ "\n" ^
                                                "push qword [rax + TYPE_SIZE] \n" ^
                                                "call qword [rax + TYPE_SIZE + WORD_SIZE] \n" ^
                                                "add rsp , 8 * 1 \n" ^
                                                "pop rbx \n" ^
                                                "shl rbx , 3 \n" ^
                                                "add rsp , rbx \n"
                                                        
                    | ApplicTP' (_e , _args) -> (applic_tp_gen _e _args)

                    | _ -> raise X_syntax_error 
            
                    
        and applic_tp_gen _e _args = 
            let applic_tp_loop_label = "applic_tp_loop" ^ (string_of_int !applic_tp_counter) in
            (increment_counter applic_tp_counter) ; 
            let folder element acc = (acc ^ (gen element) ^ "\n" ^ "push rax \n") in
                let push_args_str = (List.fold_right folder _args "") in
                    push_args_str ^ "push " ^ (string_of_int (List.length _args)) ^ "\n" ^
                    (gen _e) ^ "\n" ^
                    "push qword [rax + TYPE_SIZE] \n" ^
                    "push qword [rbp + WORD_SIZE] \n" ^
                    "mov r15 , rax \n" ^
                    "push qword [rbp] \n" ^
                    "mov rdi , PARAM_COUNT\n" ^
                    
                    "push rax \n"^
                    "push rbx \n" ^
                    "push rcx \n" ^
                    "mov rax , PARAM_COUNT \n" ^
                    "add rax , 4 \n" ^                    
                    "mov rcx , 0 \n" ^
                    applic_tp_loop_label ^ ": \n" ^
                    "inc rcx \n" ^
                    "dec rax \n" ^
                    "push rax \n" ^
                    "mov rax , rcx \n" ^
                    "mov rbx , rbp \n"^
                    "shl rax , 3 \n" ^
                    "sub rbx , rax \n" ^
                    "pop rax \n" ^
                    "mov rbx , [rbx] \n" ^
                    "mov [rbp + WORD_SIZE * rax] , rbx \n" ^
                    "cmp rcx , " ^ (string_of_int ((List.length _args) + 4)) ^ "\n" ^
                    "jne " ^ applic_tp_loop_label^ "\n" ^
                    
                    "pop rcx \n" ^
                    "pop rbx \n" ^
                    "pop rax \n" ^
                    
                    "push rax \n" ^
                    "mov rax , rdi \n" ^
                    "shl rax , 3 \n" ^
                    "add rax , WORD_SIZE * 4 \n" ^
                    "mov r12 , rax \n" ^
                    "pop rax \n" ^
                    "add rsp , r12 \n" ^
                    
                    "pop qword rbp \n" ^
                    "jmp [r15 + TYPE_SIZE + WORD_SIZE] \n"
                    
        in
        gen e;;
        
end;;


