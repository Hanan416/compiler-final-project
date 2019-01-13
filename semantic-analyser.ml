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

(*occurences counters:*)
let get_occ_counter = ref 0;;
let set_occ_counter = ref 0;;

(*helper & library functions:*)
let inc counter = counter := !counter + 1;;

let ext_env_helper param = 
	match param with 
	|Var'(VarParam(_var, minor)) -> Var'(VarBound(_var, 0, minor))
	|Var'(VarBound(_var, major, minor)) -> Var'(VarBound(_var, major+1, minor))
	|Var'(VarFree(_var)) -> raise X_syntax_error
	|_ -> raise X_syntax_error ;;

let ext_env vars_to_box = List.map ext_env_helper vars_to_box;;

let rec lst_product l1 l2 = match l1, l2 with
    | [], _ | _, [] -> []
    | h1::t1, h2::t2 -> (h1,h2) :: (lst_product [h1] t2) @ (lst_product t1 l2);; 

let rec has_all_fixed_points l1 = match l1 with 
  | [] -> true 
  | (x,y) :: rest -> if(x <> y) then false else (has_all_fixed_points rest);;

let not_empty lst = not(List.length(lst) == 0);;

let get_minor_of_param param params = 
  let rec get_minor_rec param_lst acc = 
      match param_lst with
        | [] -> -1 
        | p :: rest -> if(String.equal p param) then acc else (get_minor_rec rest (acc + 1)) 
  in get_minor_rec params 0;; 

let wrap_param_as_var_param param params = 
  Var'(VarParam(param, get_minor_of_param param params)) ;;

let rewrite_in_box_form var_tag_param = match var_tag_param with
  | Var'(VarParam(_var,minor)) -> Set'(Var'(VarParam(_var,minor)), Box'(VarParam(_var,minor)))
  |_ -> raise X_syntax_error;;

(* let fold_user_defined acc reducer lst = match lst with 
  | [] -> []
  | h :: t -> (reducer acc h) @ fold_user_defined  *)

(*---------------------------The Boxing Algorithm:-------------------------------------*)

let wrap_var_in_box _var vars_to_box = 
  if(List.mem (Var'(_var)) vars_to_box)
    then BoxGet'(_var)
  else (Var'(_var)) ;;

let rec box_set_rec e vars_to_box = 
	let app_expr e = box_set_rec e vars_to_box in 
	match e with
        | Const'(c) ->  Const'(c)
        | Var'(_var) -> wrap_var_in_box _var vars_to_box
        | If' (test ,conseq , alt) -> wrap_if_in_box test conseq alt vars_to_box
        | Set' (_var, _val) -> wrap_set_in_box _var _val vars_to_box
        | Def' (_var, _val) ->  Def' (_var, (app_expr _val))
        | Seq' (exps) ->  Seq' (List.map app_expr exps)
        | Or' (exps) ->  Or' ((List.map app_expr exps))
        | LambdaSimple' (params, body) -> wrap_lambda_s_in_box params body vars_to_box
        | LambdaOpt' (params, opt ,body) -> wrap_lambda_opt_in_box params opt body vars_to_box
        | Applic' (expr, args) -> Applic' ((app_expr expr),(List.map app_expr args))
        | ApplicTP'(expr, args)-> ApplicTP' ((app_expr expr),(List.map app_expr args))
        | _ -> raise X_syntax_error

	and wrap_set_in_box _var _val vars_to_box = 
	match _var with
	|Var'(v)->
	  let boxed_val = box_set_rec _val vars_to_box in
	    if(List.mem _var vars_to_box) 
	      then BoxSet'(v, boxed_val)
	    else Set' (_var, boxed_val)
	|_ -> raise X_syntax_error

	and wrap_if_in_box test conseq alt vars_to_box = 
		If'((box_set_rec test vars_to_box),(box_set_rec conseq vars_to_box) ,(box_set_rec alt vars_to_box))

	and wrap_lambda_s_in_box params body vars_to_box = LambdaSimple' (params, (boxing_pipeline params body vars_to_box))

	and wrap_lambda_opt_in_box params opt body vars_to_box = LambdaOpt' (params, opt, (boxing_pipeline (params @[opt]) body vars_to_box))

	and boxing_pipeline params body vars_to_box = 
    let extended_env = ext_env vars_to_box in 
    let candidates_params = (get_box_candidates params body) in
    let candidates = extended_env @ candidates_params  in
    let boxed_body_pre = box_set_rec body candidates in
    let boxed_body_post = box_add_on boxed_body_pre candidates_params in
    boxed_body_post

  and get_box_candidates params body = 
    let func param = 
      let wrapped_param = wrap_param_as_var_param param params in
          if(should_box wrapped_param body) then [wrapped_param] else [] in
    let reducer acc element = acc @ (func element)
    in
    List.fold_left reducer [] params 


  and box_add_on boxed_body_pre candidates = 
      let transformed_candidates = List.map rewrite_in_box_form candidates in
        if(not(not_empty transformed_candidates)) 
        then boxed_body_pre 
        else Seq'(transformed_candidates @ [boxed_body_pre])


	and should_box param body = 
    get_occ_counter := 0;
    let get_occ_lst = get_occ param body in
    set_occ_counter := 0; 
    let set_occ_lst = set_occ param body in 
		(should_box_predicate get_occ_lst set_occ_lst)

  and should_box_predicate get_occ_lst set_occ_lst = 
    (not_empty get_occ_lst) && (not_empty set_occ_lst) && 
    not (has_all_fixed_points (lst_product get_occ_lst set_occ_lst))

	and get_occ param body = 
		(*inner applications:*)
		let app_expr e = get_occ param e in
		(*inner handlers:*)
		let var_handler _var = if(expr'_eq param (Var'(_var))) then [-1] else [] in
		let if_handler test conseq alt = app_exprs param [test;conseq;alt] get_occ in
    let applic_handler app args = app_exprs param ([app] @ args) get_occ in
		match body with 
			| Const'(_) -> []
			| Var'(_var) -> var_handler _var 
			| If' (test ,conseq , alt) -> (if_handler test conseq alt) 
			| Set' (Var'(_var), _val) ->  (app_expr _val) 
			| Def' (_var, _val) -> (app_expr _val)
			| Seq' (exps) -> (app_exprs param exps get_occ)
			| Or' (exps) -> (app_exprs param exps get_occ)
			| LambdaSimple' (l_params, inner_body) -> occ_lambda_handler param inner_body get_occ_counter get_occ (* get_occ_lambda_handler param inner_body *)
			| LambdaOpt' (l_params, opt ,inner_body) -> occ_lambda_handler param inner_body get_occ_counter get_occ (* get_occ_lambda_handler param inner_body *)
			| Applic' (app, args) -> (applic_handler app args)
			| ApplicTP'(app, args)-> (applic_handler app args)
	    | _ -> raise X_syntax_error


  and app_exprs param lst occ_func = match lst with
      | [] -> []
      | h :: t -> (occ_func param h) @ (app_exprs param t occ_func)


  and set_occ param body = 
    (*inner applications:*)
    let app_expr e = set_occ param e in
    (*inner handlers:*)
    let if_handler test conseq alt = app_exprs param [test;conseq;alt] set_occ in
    let applic_handler app args = app_exprs param ([app] @ args) set_occ in
    let set_handler _var _val = let occ_val_lst = app_expr _val in 
                                  if(expr'_eq param (Var'(_var))) then 
                                    [-1] @ occ_val_lst 
                                  else occ_val_lst
    in
    match body with 
      | Const'(_) -> []
      | Var'(_var) -> []
      | If' (test ,conseq , alt) -> (if_handler test conseq alt) 
      | Set' (Var'(_var), _val) ->  (set_handler _var _val) 
      | Def' (_var, _val) -> (app_expr _val)
      | Seq' (exps) -> (app_exprs param exps set_occ)
      | Or' (exps) -> (app_exprs param exps set_occ)
      | LambdaSimple' (l_params, inner_body) -> occ_lambda_handler param inner_body set_occ_counter set_occ 
      | LambdaOpt' (l_params, opt ,inner_body) -> occ_lambda_handler param inner_body set_occ_counter set_occ
      | Applic' (app, args) -> (applic_handler app args)
      | ApplicTP'(app, args)-> (applic_handler app args)
      | _ -> raise X_syntax_error

  and occ_lambda_handler param body counter occ_func =
  incr counter;
  let curr_occ_counter = !counter in
  let param_to_bound = ext_env_helper param in
  let occ_in_body = occ_func param_to_bound body in
  if(occ_in_body == [])then [] else [curr_occ_counter]


let box_set e = box_set_rec e [] ;; 


let run_semantics expr =
	box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;


end;; (* struct Semantics *)