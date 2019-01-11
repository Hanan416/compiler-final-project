#use "code-gen.ml";;



let file_to_string f =
  let ic = open_in f in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s;;

let string_to_asts s = List.map Semantics.run_semantics
                         (Tag_Parser.tag_parse_expressions
                            (Reader.read_sexprs s));;

let primitive_names_to_labels = 
  ["boolean?", "is_boolean"; "float?", "is_float"; "integer?", "is_integer"; "pair?", "is_pair";
   "null?", "is_null"; "char?", "is_char"; "vector?", "is_vector"; "string?", "is_string";
   "procedure?", "is_procedure"; "symbol?", "is_symbol"; "string-length", "string_length";
   "string-ref", "string_ref"; "string-set!", "string_set"; "make-string", "make_string";
   "vector-length", "vector_length"; "vector-ref", "vector_ref"; "vector-set!", "vector_set";
   "make-vector", "make_vector"; "symbol->string", "symbol_to_string"; 
   "char->integer", "char_to_integer"; "integer->char", "integer_to_char"; "eq?", "is_eq";
   "+", "bin_add"; "*", "bin_mul"; "-", "bin_sub"; "/", "bin_div"; "<", "bin_lt"; "=", "bin_equ";
    "apply" , "apply" ; "car" , "car" ; "cdr" , "cdr" ; "cons" , "cons" ; "set-car!" , "set_car" ; "set-cdr!" , "set_cdr"];;


let make_prologue consts_tbl fvars_tbl = 
  let get_const_address const = (string_of_int (retrieve_const_offset const consts_tbl)) in
  let get_fvar_address const = (string_of_int (retrieve_fvar_label const fvars_tbl)) in
  let make_primitive_closure (prim, label) =
"    MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, " ^ label  ^ ")
    mov [fvar_tbl + " ^ (get_fvar_address prim)  ^ "], rax" in
  let make_constant ((c, a), s) = s in
  
"
;;; All the macros and the scheme-object printing procedure
;;; are defined in compiler.s
%include \"compiler.s\"

section .bss
malloc_pointer:
    resq 1

section .data
const_tbl:
" ^ (String.concat "\n" (List.map make_constant consts_tbl)) ^ "

;;; These macro definitions are required for the primitive
;;; definitions in the epilogue to work properly
%define SOB_VOID_ADDRESS " ^ "const_tbl+" ^ get_const_address Void ^ "
%define SOB_NIL_ADDRESS " ^ "const_tbl+" ^ get_const_address (Sexpr Nil) ^ "
%define SOB_FALSE_ADDRESS " ^ "const_tbl+" ^get_const_address (Sexpr (Bool false)) ^ "
%define SOB_TRUE_ADDRESS " ^ "const_tbl+" ^ get_const_address (Sexpr (Bool true))  ^ "

fvar_tbl:
" ^ (String.concat "\n" (List.map (fun _ -> "dq T_UNDEFINED") fvars_tbl)) ^ "

global main
section .text
main:
    push rbp
    mov rbp , rsp
    ;; set up the heap
    mov rdi, GB(4)
    call malloc
    mov [malloc_pointer], rax

    ;; Set up the dummy activation frame
    ;; The dummy return address is T_UNDEFINED
    ;; (which a is a macro for 0) so that returning
    ;; from the top level (which SHOULD NOT HAPPEN
    ;; AND IS A BUG) will cause a segfault.
    push 0
    push qword SOB_NIL_ADDRESS
    push qword T_UNDEFINED
    push rsp
    call code_fragment
    add rsp , 4 *8
    leave
    ret


code_fragment:
    push rbp
    mov rbp , rsp
    ;; Set up the primitive stdlib fvars:
    ;; Since the primtive procedures are defined in assembly,
    ;; they are not generated by scheme (define ...) expressions.
    ;; This is where we emulate the missing (define ...) expressions
    ;; for all the primitive procedures.
" ^ (String.concat "\n" (List.map make_primitive_closure primitive_names_to_labels)) ^ "
 
for_debug:
 ";;

(*WARNING: has high use of the given code!!!!*)

let epilogue = "
    car: 
      push rbp
      mov rbp, rsp

      mov rsi, PVAR(0)
      CAR rax, rsi 
      
      leave
      ret

    cdr:
      push rbp
      mov rbp, rsp

      mov rsi, PVAR(0)
      CDR rax, rsi 
      
      leave
      ret

    cons:
      push rbp
      mov rbp, rsp

      mov rsi, PVAR(0)
      mov rdi, PVAR(1)
      MAKE_PAIR(rax, rsi, rdi)
      
      leave
      ret

    set_car: 
      push rbp
      mov rbp, rsp

      mov rsi, PVAR(0)
      mov rdi, PVAR(1)
      
      mov [rsi + TYPE_SIZE], rdi

      mov rax, SOB_VOID_ADDRESS
      
      leave
      ret

    set_cdr: 
      push rbp
      mov rbp, rsp

      mov rsi, PVAR(0)
      mov rdi, PVAR(1)
      
      mov [rsi + TYPE_SIZE + WORD_SIZE] , rdi

      mov rax, SOB_VOID_ADDRESS
      
      leave
      ret
      
      apply:
      
      push rbp
      mov rbp , rsp
      mov r13 , 0
      mov r15 , PARAM_COUNT
      dec r15
      mov rdi , PVAR(r15)
      
      flatten_list_into_stack:
      
      cmp rdi , T_NIL
      je reverse_list
      
      inc r13
      CAR r14 , rdi
      push r14
      CDR rdi , rdi
      jmp flatten_list_into_stack
      
      reverse_list:
      mov r12 , rsp
      dec r13
      lea r11 , [rsp + 8 * r13]
      cmp r11 , r12
      jge push_other_params
      
      mov r9 , [r11]
      mov r10 , [r12]
      mov [r11] , r10
      mov [r12] , r9
   
      sub r11 , WORD_SIZE   
      add r12 , WORD_SIZE
      jmp flatten_list_into_stack
      
      push_other_params:
      sub r15 , 2
      cmp r15 , 0
      jle shift
      mov rdi , PVAR()
      shift:
      
      
      
    ";;

exception X_missing_input_file;;

try
  let infile = Sys.argv.(1) in
  let code =  (*(file_to_string "stdlib.scm") ^*) (file_to_string infile) in
  let asts = string_to_asts code in
  let consts_tbl = Code_Gen.make_consts_tbl asts in
  let fvars_tbl = Code_Gen.make_fvars_tbl asts in
  let generate = Code_Gen.generate consts_tbl fvars_tbl in
  let code_fragment = String.concat "\n\n"
                        (List.map
                           (fun ast -> (generate ast) ^ "\n    call write_sob_if_not_void \n")
                           asts) in
  let provided_primitives = file_to_string "prims.s" in                   
    print_string ((make_prologue consts_tbl fvars_tbl)  ^
                  code_fragment ^ "leave\n ret\n" ^
                    provided_primitives ^ "\n" ^ epilogue)

with Invalid_argument(x) -> raise X_missing_input_file;;
