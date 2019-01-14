(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "reader.ml";;

open PC

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];; 

(* work on the tag parser starts here *)


(*utillties: *)

let syn_err _ = raise X_syntax_error;; 

let disj_tag tp1 tp2 = fun s -> try tp1 s 
                            with X_syntax_error -> 
                                tp2 s;;
                                    
let dis_tag_list tp_list sexp = (List.fold_right disj_tag tp_list syn_err) sexp;;

let compress lst = List.sort_uniq String.compare lst ;;
    
let has_duplicates lst = (List.compare_lengths (compress lst) lst) <> 0;;

(*/--------------------------Constants: -----------------------/*)
(* TODO: check with unqoute & unqoute&spliced *)
let _constants_  sexp = match sexp with
                            | Nil -> Const(Void)
                            | Bool(e) -> Const (Sexpr(sexp))
                            | Number(e) -> Const (Sexpr(sexp))
                            | Char(e) -> Const (Sexpr(sexp))
                            | String(e) -> Const(Sexpr(sexp))
                            | Pair(Symbol("quote"), Pair(e, Nil)) -> Const(Sexpr(e))
                            | _ -> raise X_syntax_error;;
                            
(*/--------------------------Variables: -----------------------/*)

let _variables_ sexp = match sexp with 
                            | Symbol(e) -> if not(List.mem e reserved_word_list) then Var(e) else raise X_syntax_error
                            | _ -> raise X_syntax_error;;

(*/--------------------------Quasiauote: -----------------------/*)

let rec _nested_pair s_list = match s_list with 
                            | [] -> Nil
                            | head :: tail -> Pair(head, (_nested_pair tail));;

let rec _quasiquote_ sexp = match sexp with 
                            | Pair(Symbol("unquote"), Pair(e, Nil)) -> e
                            | Pair(Symbol("unquote-splicing"), Pair(e, Nil)) -> raise X_syntax_error
                            | Symbol(s) -> (Pair(Symbol("quote"), Pair(Symbol(s), Nil)))
                            | Nil -> (Pair(Symbol("quote"), Pair(Nil, Nil)))
                            | Vector(v) -> (Pair(Symbol("vector"),(_nested_pair(List.map _quasiquote_ v))))
                            | Pair(Pair(Symbol("unquote-splicing"),Pair(a, Nil)), b) -> Pair(Symbol("append"), Pair(a, Pair((_quasiquote_ b),Nil)))
                            | Pair(a, Pair(Symbol("unquote-splicing"), Pair(b, Nil))) -> Pair(Symbol("cons"), Pair(_quasiquote_ a, Pair(b, Nil)))
                            | Pair(a,b) -> Pair(Symbol("cons"), Pair(_quasiquote_ a, Pair( _quasiquote_ b, Nil)))
                            | _ -> sexp;;

let _quasiquote_header_ sexp = match sexp with 
                            | Pair(Symbol("quasiquote"), Pair(tail, Nil)) -> _quasiquote_ tail 
                            | _ -> raise X_syntax_error;;

                            


let rec _expr_ sexp = dis_tag_list [_constants_ ;_variables_ ;_conditionals_; _disjunction_; _define_; _set_bang_; _ex_sequence_;
                                    _apply_ ; _conjunctions_; _quasiquote_apply_;_cond_;_letrec_; _let_;_let_kleene_star_;_lambda_opt_; _lambda_variadic_; _lambda_simple_;] sexp

(*/--------------------------Conditionals: ---------------------/*)
    and _conditionals_ sexp = match sexp with 
                            | Pair(Symbol("if"), Pair(test, Nil)) -> raise X_syntax_error
                            | Pair(Symbol("if"), Pair(test, Pair(th, Pair(alt, Nil)))) -> If((_expr_ test), (_expr_ th), (_expr_ alt))
                            | Pair(Symbol("if"), Pair(test, Pair(th, Nil))) -> If ((_expr_ test), (_expr_ th), Const(Void))
                            |  _ -> raise X_syntax_error
    
(*/--------------------------Disjunction: ---------------------/*)
    and _disjunction_helper_ sexp = match sexp with 
                            | Pair(Symbol("or"), Nil) -> [Const(Sexpr(Bool(false)))]
                            | Pair(Symbol("or"), Pair(e, Nil)) -> [_expr_ e]
                            | Pair(Symbol("or"), Pair(e, tail)) -> ([_expr_ e] @ (_disjunction_helper_ (Pair(Symbol("or"), tail))))
                            | _ -> raise X_syntax_error
    
    and _disjunction_ sexp = 
      let lst = _disjunction_helper_ sexp in 
        if (List.length lst) > 1 
          then Or(lst)
          else match lst with 
                            | [e] -> e
                            | [] -> Const(Sexpr(Bool(false)))
                            | _ -> raise X_syntax_error
    
(*/--------------------------Define: ---------------------/*)
    and _define_ sexp = match sexp with 
                            | Pair(Symbol("define"), Pair(Pair(v, params), body)) ->  Def(_variables_ v, _expr_ (Pair(Symbol("lambda"), Pair(params, body))))
                            | Pair(Symbol("define"), Pair(v, Pair(e, Nil))) -> Def((_variables_ v),(_expr_ e))
                            | _ -> raise X_syntax_error
                            
(*/--------------------------Assignment: ---------------------/*)
    and _set_bang_ sexp = match sexp with 
                            | Pair(Symbol("set!"), Pair(v, Pair(e, Nil))) -> Set((_variables_ v),(_expr_ e))
                            | _ -> raise X_syntax_error
                            
(*/--------------------------Sequences: ---------------------/*)
    
    and ex_sequence_helper sexp = match sexp with 
                            | Pair(Symbol("begin"), Nil) -> [Const(Void)]
                            | Pair(Symbol("begin"), Pair(e, Nil)) -> [_expr_ e]
                            | Pair(Symbol("begin"), Pair(e, tail)) -> ([_expr_ e] @ (ex_sequence_helper (Pair(Symbol("begin"), tail))))
                            | _ -> raise X_syntax_error
    
    
    and _ex_sequence_ sexp = match sexp with 
                            | Pair(Symbol("begin"), Nil) -> Const(Void)
                            | Pair(Symbol("begin"), Pair(e, Nil)) -> _expr_ e
                            | Pair(Symbol("begin"), Pair(e, tail)) -> Seq(ex_sequence_helper(sexp))
                            | _ -> raise X_syntax_error
                          
    
(*/--------------------------Application: ---------------------/*)
    
    and apply_helper sexp = match sexp with 
                            | Pair(param, Nil) -> [_expr_ param]
                            | Pair(param, tail) -> ([_expr_ param] @ apply_helper(tail))
                            | _-> raise X_syntax_error
    
    and _apply_ sexp = match sexp with 
                            | Pair(name, Nil) -> Applic(_expr_ name, [])
                            | Pair(name, rest) -> Applic(_expr_ name, (apply_helper rest))
                            | _-> raise X_syntax_error
                            
(*/--------------------------Lambda: ---------------------/*)

    and _convert_nested_pair_to_str_list nester_pair = match nester_pair with 
                            | Nil -> []
                            | Pair (Symbol(p), Symbol(pp)) -> [p; pp]
                            | Pair(Symbol(param), Nil) -> [param]
                            | Pair(Symbol(param), tail) -> [param] @ (_convert_nested_pair_to_str_list tail)
                            | _ -> raise X_syntax_error

    and _extract_opt_params_ lst = match lst with 
                            | Pair(Symbol(s), Symbol(vs)) -> vs
                            | Pair(Symbol(s), Nil) -> ""
                            | Pair(Symbol(s), rest) -> _extract_opt_params_ rest 
                            | _ -> raise X_syntax_error

    and _lambda_simple_ sexp = match sexp with
                            | Pair(Symbol("lambda"), Pair(params, Nil)) -> raise X_syntax_error
                            | Pair(Symbol("lambda"), Pair(params, body)) -> _lambda_simple_helper params body
                            | _ -> raise X_syntax_error
                            
    and _lambda_opt_ sexp = match sexp with 
                            | Pair(Symbol("lambda"), Pair(params, body)) -> (let vs = _extract_opt_params_ params in 
                                                                            if (vs = "") then raise X_syntax_error
                                                                                         else _lambda_opt_helper params vs body)
                            | _ -> (raise X_syntax_error)

    and _lambda_variadic_ sexp = match sexp with 
                            | Pair(Symbol("lambda"), Pair(Pair(Symbol("quote"), Pair(Nil, Nil)), body)) -> _lambda_opt_helper Nil "" body
                            | Pair(Symbol("lambda"), Pair(Symbol(vs),body)) -> _lambda_opt_helper Nil vs body
                            | _ -> raise X_syntax_error
    

    and _lambda_simple_helper params body = 
      let params_strlst = (_convert_nested_pair_to_str_list params) in 
      if not (has_duplicates params_strlst) 
        then LambdaSimple(params_strlst, (_ex_sequence_ (Pair(Symbol("begin"), body)))) 
        else raise X_syntax_error

    and _lambda_opt_helper man_params opt_params body = 
      let all_params = (_convert_nested_pair_to_str_list man_params) in
      let params_strlst = (List.filter (fun (e)-> e <> opt_params) (all_params)) in
      if (not (has_duplicates all_params))
        then  (LambdaOpt(params_strlst, opt_params, (_ex_sequence_ (Pair(Symbol("begin"), body)))))
        else  (raise X_syntax_error)


(*/--------------------------Macro expansion: ---------------------/*)

  (*/--------------------------Conjunctions: ---------------------/*)

  and _conjunctions_ sexp  = match sexp with 
                            | Pair(Symbol("and"), Nil) -> Const(Sexpr(Bool(true)))
                            | Pair(Symbol("and"), Pair(e, Nil)) -> _expr_ e
                            | Pair(Symbol("and"), Pair(e, tail)) -> _expr_ (Pair (Symbol "if", Pair (e, Pair(Pair (Symbol "and", tail), Pair (Bool false, Nil)))))
                            | _ -> raise X_syntax_error


  (*/--------------------------Quasiquote: ---------------------/*)

  and _quasiquote_apply_ sexp = match sexp with 
                            | Pair(Symbol("quasiquote"), rest) -> _expr_ (_quasiquote_header_ sexp)
                            | _ -> raise X_syntax_error

  (*/--------------------------Let: ---------------------/*)

  and extract_vars params_vals = match params_vals with
                            | Pair(Pair(Symbol(v1), Pair(exp1, Nil)), Nil) -> Pair(Symbol(v1), Nil)
                            | Pair(Pair(Symbol(v1), Pair(exp1, Nil)), rest) -> Pair(Symbol(v1), (extract_vars rest))
                            | _ -> raise X_syntax_error 

  and extract_vals params_vals = match params_vals with
                            | Pair(Pair(Symbol(v1), Pair(exp1, Nil)), Nil) -> Pair(exp1, Nil)
                            | Pair(Pair(Symbol(v1), Pair(exp1, Nil)), rest) -> Pair(exp1, (extract_vals rest))
                            | _ -> raise X_syntax_error 


  and _let_helper_ params_vals body = match params_vals with 
                            | Nil -> Pair(Pair(Symbol("lambda"), Pair(Nil, body)), Nil)
                            | Pair(head, tail) -> (let vars = extract_vars params_vals in 
                                                  let vals = extract_vals params_vals in 
                                                  Pair(Pair(Symbol("lambda"), Pair(vars, body)), vals))
                            | _ -> raise X_syntax_error

  and _let_ sexp = match sexp with 
                            | Pair (Symbol("let"), Pair (params, body)) -> (_expr_( _let_helper_ params body))
                            | _ -> raise X_syntax_error

  (*/--------------------------Let*: ---------------------/*)

  and _let_kleene_star_helper_ params_vals body  = match params_vals with 
                            | Nil -> Pair(Symbol("let"), Pair(params_vals, body))
                            | Pair(exp, Nil) -> Pair(Symbol("let"), Pair(Pair(exp, Nil), body))
                            | Pair(exp,rest) -> Pair(Symbol("let"), Pair(Pair(exp, Nil), Pair(Pair(Symbol("let*"), Pair(rest, body)), Nil)))
                            | _ -> raise X_syntax_error

  and _let_kleene_star_ sexp = match sexp with 
                            | Pair(Symbol("let*"), Pair(params, body)) -> (_expr_(_let_kleene_star_helper_ params body))
                            | _-> raise X_syntax_error 

  (*/--------------------------Letrec: ---------------------/*)

  and _init_letrec_ params = match params with 
                            | Pair(Pair(Symbol(var), Pair(expr, Nil)), Nil) -> Pair(Pair(Symbol(var), Pair(Pair(Symbol("quote"), Pair(Symbol("whatever"), Nil)), Nil)), Nil)
                            | Pair(Symbol(var), expr) -> Pair(Pair(Symbol(var), Pair(Pair(Symbol("quote"), Pair(Symbol("whatever"), Nil)), Nil)), Nil)
                            | Pair(Pair(Symbol(var), Pair(expr, Nil)), rest) -> Pair(Pair(Symbol(var), Pair(Pair(Symbol("quote"), Pair(Symbol("whatever"), Nil)), Nil)), _init_letrec_ rest)
                            | _-> raise X_syntax_error

  and _build_letrec_body params body = match params with 
                            | Pair(Pair(Symbol(var), Pair(expr, Nil)), Nil) -> Pair(Pair(Symbol("set!"), Pair(Symbol(var), Pair(expr, Nil))), body)
                            | Pair(Symbol(var), Pair(expr,Nil)) -> Pair(Pair(Symbol("set!"), Pair(Symbol(var), Pair(expr, Nil))), body)
                            | Pair(Pair(Symbol(var), Pair(expr, Nil)), rest) -> Pair(Pair(Symbol("set!"), Pair(Symbol(var), Pair(expr, Nil))), _build_letrec_body rest body)
                            | _ -> raise X_syntax_error

  and _letrec_helper_ params_vals body = match params_vals with
                            | Nil -> Pair(Symbol("let"), Pair(params_vals, body))
                            | Pair(exp, rest) -> Pair(Symbol("let"), Pair((_init_letrec_ params_vals), (_build_letrec_body params_vals body)))
                            | _ -> raise X_syntax_error


  and _letrec_ sexp = match sexp with 
                            | Pair(Symbol("letrec"), Pair(params, body)) -> (_expr_ (_letrec_helper_ params body))
                            | _ -> raise X_syntax_error

  (*/--------------------------Cond: ---------------------/*)
  
  and _cond_arrow_form_base e e_f =  Pair(Symbol "let", Pair(Pair(Pair(Symbol "value", Pair(e, Nil)), Pair(Pair(Symbol "f", 
                                Pair(Pair(Symbol "lambda", Pair(Nil,Pair(e_f, Nil))), Nil)), Nil)),Pair(Pair(Symbol "if", 
                                Pair(Symbol "value", Pair(Pair(Pair(Symbol "f", Nil), Pair(Symbol "value", Nil)), Nil))), Nil))) 

  and _cond_arrow_form_rec e e_f rest = Pair(Symbol "let", Pair(Pair(Pair(Symbol "value", Pair(e, Nil)), 
                                  Pair(Pair(Symbol "f", Pair(Pair(Symbol "lambda", Pair(Nil, Pair(e_f, Nil))), Nil)), 
                                  Pair(Pair(Symbol "rest", Pair(Pair(Symbol "lambda", Pair(Nil, Pair((_cond_helper_ rest),Nil))), Nil)), Nil))),
                                  Pair(Pair(Symbol "if", Pair(Symbol "value", Pair(Pair(Pair(Symbol "f", Nil), Pair(Symbol "value", Nil)), 
                                  Pair(Pair(Symbol "rest", Nil), Nil)))), Nil)))

  and _cond_helper_ ribs = match ribs with 
                            | Pair(Pair(e, Pair(Symbol("=>"), Pair(e_f, Nil))), Nil) -> _cond_arrow_form_base e e_f
                            | Pair(Pair(e, Pair(Symbol("=>"), Pair(e_f, Nil))), rest) -> _cond_arrow_form_rec e e_f rest
                            | Pair(Pair(Symbol("else"), e_n), Nil) -> Pair(Symbol ("begin"), e_n)
                            | Pair(Pair(e, e_n), rest) -> Pair(Symbol "if", Pair(e, Pair(Pair(Symbol "begin", e_n), Pair((_cond_helper_ rest),Nil))))
                            | Nil -> Nil
                            | _ -> raise X_syntax_error


  and _cond_ sexp = match sexp with 
                            | Pair(Symbol("cond"), ribs) -> (_expr_ (_cond_helper_ ribs))
                            | _ -> raise X_syntax_error

  
let tag_parse_expression sexpr = _expr_ sexpr;;

let tag_parse_expressions sexpr = List.map _expr_ sexpr ;;
  
end;; (* struct Tag_Parser *)
