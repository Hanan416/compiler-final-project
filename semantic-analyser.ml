(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)
#use "reader.ml";;
#use "tag-parser.ml";;

open Reader ;;
open Tag_Parser ;;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
  (* val get_occ_tuple : string -> expr' -> (string, int list, int list)  *)
end;;

module Semantics : SEMANTICS = struct

let create_bound_env _vars=
    let rec helper index lst = 
        match lst with
            | [] -> []
            | [_var] -> [Var'(VarBound(_var , 0 , index))]
            | car :: cdr -> [Var'(VarBound(car , 0 , index))] @ (helper (index+1) cdr) in
        (helper 0 _vars);;

let extend_bound_vars _bound_vars =
    let rec helper _vars=
        match _vars with
            |Var'(VarBound(_var , _majorIdx , _minorIdx)) -> Var'(VarBound(_var , (_majorIdx+1) , _minorIdx))
            | _ ->raise X_syntax_error in
        (helper _bound_vars);;
            
let get_var_param _var _params = 
    let rec helper _params _index = 
        match _params with
        | [] -> Const'(Sexpr(Nil))
        |  car :: cdr ->
            if((compare car _var) == 0)
                then Var'(VarParam(_var , _index))
                else (helper cdr (_index+1)) in
        (helper _params 0);;
        
let get_var_bound _var _bound =
    let rec helper _bounds = 
        match _bounds with
        | [] -> Const'(Sexpr(Nil))
        | Var'(VarBound(_var_name , _majorIdx , _minorIdx)) :: cdr ->
            if((compare _var _var_name) == 0)
                then Var'(VarBound(_var_name , _majorIdx , _minorIdx))
                else (helper cdr) 
        | _ -> raise X_syntax_error in
        (helper _bound);;
    
let annotate_var _var _params _bound = 
    let var_param = (get_var_param _var _params) in
        if(not (expr'_eq var_param (Const'(Sexpr(Nil)))))
            then var_param
            else let var_bound = (get_var_bound _var _bound) in
                if(not (expr'_eq var_bound (Const'(Sexpr(Nil)))))
                    then var_bound 
                    else Var'(VarFree(_var));;
                    
let rec annotate e _params _bound= 
    let annotate_expr _expr = (annotate _expr _params _bound) in
        match e with
        | Const(_c) -> Const' (_c)
        | Var(_v) -> (annotate_var _v _params _bound)
        | If(_test , _then , _else) -> If' ((annotate_expr _test) , (annotate_expr _then) , (annotate_expr _else))
        | Seq(_l) -> Seq'(List.map annotate_expr _l)
        | Set(_var , _val) -> Set'((annotate_expr _var) , (annotate_expr _val))
        | Def(_var , _val) -> Def'((annotate_expr _var) , (annotate_expr _val))
        | Or(_l) -> Or'(List.map annotate_expr _l);
        | Applic(_e , _args) -> Applic'((annotate_expr _e) , (List.map annotate_expr _args))
        | LambdaSimple(_vars , _body) -> LambdaSimple'(_vars , (annotate _body _vars ((create_bound_env _params) @ (List.map extend_bound_vars _bound))))
        | LambdaOpt(_vars , _opt , _body) -> LambdaOpt'(_vars , _opt , (annotate _body (_vars @ [_opt]) ((create_bound_env _params) @ (List.map extend_bound_vars _bound))));;
                                                            
let annotate_lexical_addresses e = (annotate e [] []);;

let get_last lst = 
  let reversed = (List.rev lst) in
  let last = (List.hd reversed) in
  let rest = (List.rev (List.tl reversed)) in
  (last, rest);;

let rec aux_param_annotate_tail_calls e in_tp = 
  match e with
        | Const'(c) -> Const'(c)
        | Var'(var) -> Var'(var)
        | If' (test ,conseq , alt) -> If' ((aux_param_annotate_tail_calls test false) ,(aux_param_annotate_tail_calls conseq in_tp) ,(aux_param_annotate_tail_calls alt in_tp))
        | Seq' (exps) ->  Seq'(sequence_handler exps in_tp) (*CHANGE seqOrHandler *)
        | Set' (_var, _val) -> Set' ((aux_param_annotate_tail_calls _var false), (aux_param_annotate_tail_calls _val false))
        | Def' (_var, _val) -> Def' ((aux_param_annotate_tail_calls _var false), (aux_param_annotate_tail_calls _val false))
        | Or' (exps) -> Or' (or_handler exps in_tp)
        | LambdaSimple' (vars, body) -> LambdaSimple' (vars, (aux_param_annotate_tail_calls body true))
        | LambdaOpt' (vars, opt ,body) -> LambdaOpt' (vars, opt, (aux_param_annotate_tail_calls body true))
        | Applic' (e, args) -> (app_handler e args in_tp)(*CHANGE applicHandler*)
        | _ -> raise X_syntax_error

  and sequence_handler exps in_tp = 
    let (l, r) = get_last exps in
        (List.map hp r) @ [(aux_param_annotate_tail_calls l in_tp)]

  and or_handler exps in_tp = 
    let (l, r) = get_last exps in
        (List.map hp r) @ [(aux_param_annotate_tail_calls l in_tp)]

  and app_handler e args in_tp =
   match in_tp with
        | true -> ApplicTP'((hp e),(List.map hp args))
        | false -> Applic'((hp e),(List.map hp args))

   and hp exp = aux_param_annotate_tail_calls exp false;;

let annotate_tail_calls e = aux_param_annotate_tail_calls e false;;


(*-----------------------------------------Boxing---------------------------------- *) 

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

and 

print_sexprs = fun sexprList -> 
  match sexprList with
    | [] -> ""
    | head :: tail -> (print_sexpr head) ^ "," ^ (print_sexprs tail)

and 

print_sexprs_as_list = fun sexprList ->
  let sexprsString = print_sexprs sexprList in
    "[ " ^ sexprsString ^ " ]"

and
print_expr = fun exprObj ->
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

and

print_exprs_as_list = fun exprList ->
  let exprsString = print_exprs exprList in
    "[ " ^ exprsString ^ " ]"

and

print_strings = fun stringList -> 
  match stringList with
    | [] -> ""
    | head :: [] -> head 
    | head :: tail -> head ^ "; " ^ (print_strings tail)

and

print_strings_as_list = fun stringList ->
  let stringList = print_strings stringList in
    "[ " ^ stringList ^ " ]";;


let rec printIntList = function 
[] -> ()
| e::l -> print_int e ; print_string " " ; printIntList l

let rec printThreesomesList lst =
	match lst with
		| [] -> ()
		| (name, reads, writes)::cdr -> print_string "varName: " ; print_string name ; print_string " readlist: " ; printIntList reads ; print_string " writeList: " ; printIntList writes ; printThreesomesList cdr;;


let rec printStringList = function 
[] -> ()
| e::l -> print_string e ; print_string " " ; printStringList l ;;
(*TODO(7/1/19): add box_set to the run_semantics*)

let major_counter = ref 0 ;;

(* let inc_and_get = let _val = !major_counter + 1 in _val;;
 *)
let append_and_get lst_ref _val = let _val = !lst_ref @ [_val] in _val;; 

let str_equals str1 str2 = (compare str1 str2) == 0;;

let not_empty lst = not(List.length(lst) == 0);;

let set_diff l1 l2 = List.filter (fun x -> not (List.mem x l2)) l1;;

(*check validity*)
let rec product l1 l2 = 
    match l1, l2 with
    | [], _ | _, [] -> []
    | h1::t1, h2::t2 -> (h1,h2)::(product [h1] t2)@(product t1 l2);;

let rec has_occs_in_diff_ribs occ_p_list = 
	match occ_p_list with 
	| [] -> false 
	| (x,y) :: rest -> if(x <> y) then true else (has_occs_in_diff_ribs rest);; 

let get_var_name _var = match _var with
				| VarFree(_var) -> _var
				| VarParam(_var, minor) -> _var
				| VarBound(_var, major, minor) -> _var


let acc_occ occ_tuple_lst = 
	let rec acc_occ_rec occ_tuple_lst get_occs set_occs = 
	match occ_tuple_lst with
				| [] -> (get_occs, set_occs) 
				| (param, get_occ, set_occ) :: rest -> (acc_occ_rec rest (get_occs @ get_occ) (set_occs @ set_occ))
	in (acc_occ_rec occ_tuple_lst [] []) ;;

let get_minor_of_param param params = 
	let rec get_minor_rec param_lst acc = 
			match param_lst with
				| [] -> -1 
				| p :: rest -> if(str_equals p param) then acc else (get_minor_rec rest (acc + 1)) 
	in 
	(get_minor_rec params 0) ;;

let rewrite_in_box_form param minor = Set'(Var'(VarParam(param, minor)), Box'(VarParam(param, minor)));;

let wrap_in_box param params = 
	let minor = get_minor_of_param param params in 
	rewrite_in_box_form param minor;;

let filter_by_offset_in_list lst offset_lst = 
	let rec filter_by_offset_in_list_rec lst offset_lst ret = 
		match lst, offset_lst with
			| [], _ | _, [] -> ret 
			| h1::t1, h2::t2 -> if(h2) then 
									[h1] @ (filter_by_offset_in_list_rec t1 t2 ret) 
								else
									 (filter_by_offset_in_list_rec t1 t2 ret)
	in
	(filter_by_offset_in_list_rec lst offset_lst []);;


let ret_boxed_body boxed_body filtered_params params =  
	let wrap_in_box_wrapper param = wrap_in_box param params in 
		Seq'((List.map wrap_in_box_wrapper filtered_params) @ [boxed_body]) ;;


let rec box_set_rec e = match e with 
				| Const'(c) ->  Const'(c)
				| Var'(name) -> Var'(name)
				| If' (test ,conseq , alt) -> If' ((box_set_rec test),(box_set_rec conseq) ,(box_set_rec alt))
				| Set' (_var, _val) -> Set' ((box_set_rec _var), (box_set_rec _val))
				| Def' (_var, _val) ->  Def' ((box_set_rec _var), (box_set_rec _val))
				| Seq' (exps) ->  Seq' (List.map box_set_rec exps)
				| Or' (exps) ->  Or' ((List.map box_set_rec exps))
				| LambdaSimple' (params, body) -> LambdaSimple' (params, (boxing_pipeline params body))
				| LambdaOpt' (params, opt ,body) -> LambdaOpt' (params, opt, (boxing_pipeline (params @[opt]) body))
				| Applic' (expr, args) -> Applic' ((box_set_rec expr),(List.map box_set_rec args))
				| ApplicTP'(expr, args)-> ApplicTP' ((box_set_rec expr),(List.map box_set_rec args))
			    | _ -> raise X_syntax_error

    

    (*1. return the occurence tuple(param, get_occ, set_occ) for a given param*)
    and get_occ_tuple param body = find_occurrences param body [] [] major_counter

    (*need to implement: app_expr expr & app_exprs exprs & inner handlers*)
    and find_occurrences param body get_occ set_occ counter = 
    	(*inner applications*)
    	let app_expr expr = (find_occurrences param expr get_occ set_occ counter) in
    	let app_exprs exprs = 
    		let (_get_occ, _set_occ) = acc_occ (List.map app_expr exprs) in 
    		(param, _get_occ, _set_occ) in
    	(*inner handlers:*)
    	let ret_occ_tuple = (param, get_occ, set_occ) in
    	let var_handler var_name = 
    		if(str_equals var_name param) then 
    			(param, [-1], set_occ) 
    		else 
    			ret_occ_tuple 
    	in
    	let if_handler test conseq alt = (app_exprs [test; conseq; alt]) in 
    	let set_handler _var _val = 
    		let (param_val, get_occ_val, set_occ_val) = app_expr _val in 
    		let param_val_name = get_var_name _var in 
    		if(str_equals param_val_name param) then  
    			(param, get_occ_val, [-1])
    		else 
    			(param, get_occ_val, set_occ_val)
    	in
    	let applic_handler app args = app_exprs ([app] @ args) 
    	in
    	match body with
		    	| Const'(_) -> ret_occ_tuple
				| Var'(VarFree(_)) -> ret_occ_tuple
				| Var'(VarParam(_var, minor)) -> (var_handler _var)
				| Var'(VarBound(_var, major, minor)) -> (var_handler _var)
				| If' (test ,conseq , alt) -> (if_handler test conseq alt) 
				| Set' (Var'(_var), _val) ->  (set_handler _var _val) 
				| Def' (_var, _val) -> (app_expr _val)(*???*)
				| Seq' (exps) -> (app_exprs exps)
				| Or' (exps) -> (app_exprs exps)
				| LambdaSimple' (l_params, inner_body) -> major_counter := !major_counter + 1; (find_occ_lambda_handler l_params inner_body param get_occ set_occ ret_occ_tuple app_expr !major_counter)
				| LambdaOpt' (l_params, opt ,inner_body) -> major_counter := !major_counter + 1; (find_occ_lambda_handler (l_params @ [opt]) inner_body param get_occ set_occ ret_occ_tuple app_expr !major_counter)
				| Applic' (app, args) -> (applic_handler app args)
				| ApplicTP'(app, args)-> (applic_handler app args)
				| Box'(_) -> ret_occ_tuple
			    | BoxGet'(_) -> ret_occ_tuple
			    | BoxSet'(_, _) -> ret_occ_tuple
			    | _ -> raise X_syntax_error

    and find_occ_lambda_handler_helper boxed_inner_lambda param counter get_occ set_occ app_expr = 
		let (_param, inner_get_occ, inner_set_occ) = (app_expr boxed_inner_lambda) in
		let tot_get_occ = ref get_occ in 
		let tot_set_occ = ref set_occ in
		if ((not_empty inner_get_occ)) then 
			tot_get_occ := (append_and_get tot_get_occ counter);
		if ((not_empty inner_set_occ)) then
			tot_set_occ := (append_and_get tot_set_occ counter);
		(param, !tot_get_occ, !tot_set_occ)

	and find_occ_lambda_handler params body param get_occ set_occ ret_occ_tuple app_expr counter= 
(* 		let c_val = inc_and_get in
 *)    		if (List.mem param params) then
    			ret_occ_tuple
    		else 
				(find_occ_lambda_handler_helper (boxing_pipeline params body) param counter get_occ set_occ app_expr)


	(*2. check if the boxing process is needed for a certain occ_tuple*)
    and should_box param_occ_tuple =  
    	match param_occ_tuple with 
    			| (param, get_occ, set_occ) -> has_occs_in_diff_ribs (product get_occ set_occ)


    and boxing_procedure body filtered_params params = if(not_empty filtered_params) then 
    												let updated_body = (boxing_proc_traverse body filtered_params) in 
    													(ret_boxed_body updated_body filtered_params params)
    											else
    												(box_set_rec body)


    and boxing_proc_traverse body filtered_params = 
    			(*inner applications:*)
    			let app_expr_wrapper expr = (boxing_proc_traverse expr filtered_params) in
    			(*inner handlers*)
				let var_param_handler _var minor = if (List.mem _var filtered_params) then BoxGet'(VarParam(_var, minor)) else Var'(VarParam(_var, minor)) in
				let var_bound_handler _var major minor = if (List.mem _var filtered_params) then BoxGet'(VarBound(_var, major, minor)) else Var'(VarBound(_var, major, minor)) in
    			let if_handler test conseq alt = If'(app_expr_wrapper test, app_expr_wrapper conseq, app_expr_wrapper alt) in
    			let set_handler _var _val = let var_name = (get_var_name _var) in 
    											let applied_val = app_expr_wrapper _val in
    												if (List.mem var_name filtered_params) then 
    													BoxSet'(_var, applied_val) 
    												else Set' (Var'(_var), applied_val) 
    			in   			
    			let applic_handler app args = Applic'(app_expr_wrapper app, List.map app_expr_wrapper args) in
    			let applicTP_handler app args = ApplicTP'(app_expr_wrapper app, List.map app_expr_wrapper args) in
    			match body with
		    	| Const'(c) -> Const'(c)
				| Var'(VarFree(var)) -> Var'(VarFree(var))
				| Var'(VarParam(_var, minor)) -> (var_param_handler _var minor)
				| Var'(VarBound(_var, major, minor)) -> (var_bound_handler _var major minor)
				| If' (test ,conseq , alt) -> (if_handler test conseq alt)
				| Set' (Var'(_var), _val) -> (set_handler _var _val)
				| Def' (Var'(_var), _val) -> (boxing_proc_define_handler _var _val filtered_params)
				| Seq' (exps) -> Seq'(List.map app_expr_wrapper exps)
				| Or' (exps) -> Or' (List.map app_expr_wrapper exps)
				| LambdaSimple' (l_params, inner_body) -> (boxing_proc_lambda_s_handler l_params inner_body filtered_params)
				| LambdaOpt' (l_params, opt ,inner_body) -> (boxing_proc_lambda_o_handler l_params opt inner_body filtered_params)
				| Applic' (app, args) -> (applic_handler app args)
				| ApplicTP'(app, args)-> (applicTP_handler app args) 
				| Box'(b) -> Box'(b)
			    | BoxGet'(b) ->  Box'(b)
			    | BoxSet'(b, e) -> BoxSet'(b, e) 
			    | _ -> raise X_syntax_error

	

    and boxing_proc_define_handler _var _val filtered_params = let var_name = (get_var_name _var) in
    											let sub_filtered_params = set_diff filtered_params [var_name] in 
    												Def'(Var'(_var), (boxing_proc_traverse _val sub_filtered_params))

   	and boxing_proc_lambda_s_handler params body filtered_params = let sub_filtered_params = (printStringList filtered_params); print_string "; "; (printStringList params); 
   																	set_diff filtered_params params in
   																	(* (printStringList filtered_params); *)
   																	LambdaSimple'(params, (boxing_proc_traverse body sub_filtered_params))

   	and boxing_proc_lambda_o_handler params opt body filtered_params = let tot_params = params @ [opt] in 
   																		let sub_filtered_params = set_diff filtered_params tot_params in
   																			LambdaOpt'(params, opt, (boxing_proc_traverse body sub_filtered_params)) 

    and boxing_pipeline params body = 
    	let get_occ_tuple_wrapper param = get_occ_tuple param body in 
    	let occ_tuple_lst = List.map get_occ_tuple_wrapper params in
    	(* printThreesomesList(occ_tuple_lst); *)
    	let should_box_lst = List.map should_box occ_tuple_lst in 
    	let filtered_params = filter_by_offset_in_list params should_box_lst in
    	boxing_procedure body filtered_params params;;


let box_set e = box_set_rec e;; 


let run_semantics expr =
	box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;

  
(* print_string(print_expr (run_semantics(tag_parse_expression (read_sexpr "
          (define foo1 (lambda (x)
                          (list (lambda () x)
                                (lambda (y) 
                                  (set! x y)))))"))));;  *)

(run_semantics (LambdaSimple (["x"],
      Or [Applic (LambdaOpt (["y"], "z", Applic (LambdaSimple ([], Applic (LambdaSimple ([], 
          Applic (Var "+", [Var "x"; Var "z"])), [])), [])), [Var "x"; Const (Sexpr (Number (Int 1)))]); 
          LambdaSimple ([], Set (Var "x", Var "w")); Applic (Var "w", [Var "w"])])));;
(* print_string(printThreesomesList((get_occ_tuple "x" (ApplicTP'(VarFree("list" ),[ LambdaSimple'([  ],VarBound("x" 0 0)); LambdaSimple'([ y ],Set(VarBound("x" 0 0),VarParam("y", 0))) ])))))       *)

end;; (* struct Semantics *)


(* 

run_semantics(tag_parse_expression (read_sexpr "
          (define foo1 (lambda (x)
                          (list (lambda () x)
                                (lambda (y) 
                                  (set! x y)))))"))  *)

                             (*might have issues*)
		(*let lambda_handler_helper params body c_val = 
			let boxed_inner_lambda = (boxing_alg params body) in 
			let (_param, inner_get_occ, inner_set_occ) = (app_expr boxed_inner_lambda) in
			let tot_get_occ = ref get_occ in 
			let tot_set_occ = ref set_occ in
			if ((not_empty inner_get_occ)) then 
				tot_get_occ := (append_and_get tot_get_occ c_val);
			if ((not_empty inner_set_occ)) then
				tot_set_occ := (append_and_get tot_set_occ c_val);
			(param, tot_get_occ, tot_set_occ)
		in
    	let lambda_handler params body = 
    		let c_val = inc_and_get in
    		if (List.mem param params) then
    			ret_occ_tuple
    		else 
    			(lambda_handler_helper params body c_val) 
    	in*)