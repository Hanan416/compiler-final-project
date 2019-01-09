
(* reader.ml
 * A compiler from Scheme to x86/64
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "pc.ml";;

open PC

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
  
type number =
  | Int of int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | Vector of sexpr list;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | Vector(l1), Vector(l2) -> List.for_all2 sexpr_eq l1 l2
  | _ -> false;;
  
module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

    
(* Parser for CharPrefix: *)

let char_prefix_s = "#\\";;

let _char_prefix_ = word char_prefix_s;;

(* Parser for HexPrefix: *)

let hex_prefix_s = "#x";;

let _hex_prefix_ = word_ci hex_prefix_s;; 

(* Parser for VisibleSimpleChar: *)

let space = ' ';;

let _visible_simple_char = 
    let parse = const(fun(ch) -> ch > space) in 
    pack parse (fun(ch) -> Char(ch));;

(* Parser for NamedChar: *)

let newline = '\n';;
let nul = '\000';;
let page = '\012';;
let return = '\r';;
let tab = '\t';;
let error = 'e';;

let _named_char_ = 
    let namedChar_list = List.map word_ci ["newline";"nul";"page";"return";"tab";"space"] in
    let parse =  disj_list namedChar_list in 
    pack parse (fun(ls) -> match (list_to_string(List.map lowercase_ascii ls)) with
                                    | "newline" -> Char(newline)
                                    | "nul" -> Char(nul)
                                    | "page" -> Char(page)
                                    | "return" -> Char(return)
                                    | "tab" -> Char(tab)
                                    | "space" -> Char(space)
                                    | _ -> Char(error));;
    

(* Digits & HexDigits: *)

let _digit_ = range '0' '9';;
let _hex_letters_ = range 'a' 'f';;
let _hex_letters_CAPS_ = range 'A' 'F';;
let _hex_digit_ = disj_list [_digit_; _hex_letters_ ; _hex_letters_CAPS_];;

(* Parser for HexChar: *)

let _hex_char_ = 
    let parse = caten (char_ci 'x') (plus _hex_digit_) in 
    pack parse (fun((x,n)) -> Char(Char.chr(int_of_string("0x" ^ (list_to_string n)))));;
    

(* /---------------------------Number sub parsers -----------------------/ *)

(* Parser for Natural and HexNatural numbers: *)

let _natural_ = (plus _digit_);;
let _hex_natural_ = (plus _hex_digit_);;

(* Parser for Integer and HexInteger: *)

let _plus_ = char '+';;
let _minus_ = char '-';;

let _integer_ = 
    let parse = (caten (maybe (disj _plus_ _minus_)) _natural_) in
    pack parse (fun ((x , n)) -> match x with
                                            |Some '-' -> Number(Int(int_of_string (list_to_string n) * -1))
                                            |Some '+' -> Number(Int(int_of_string (list_to_string n)))
                                            |None -> Number(Int(int_of_string (list_to_string n)))
                                            | _ -> raise X_no_match);;                                (*check if there is a better way to do*)
                                            
let _hex_integer_ = 
    let parse = (caten _hex_prefix_ (caten(maybe (disj _plus_ _minus_)) _hex_natural_)) in
    pack parse (fun (p, (x , n)) -> match x with
                                            |Some '-' -> Number(Int(-1 * int_of_string ("0x" ^ (list_to_string n))))
                                            |Some '+' -> Number(Int(int_of_string ("0x" ^ (list_to_string n))))
                                            |None -> Number(Int(int_of_string ("0x" ^ (list_to_string n))))
                                            | _ -> raise X_no_match);;                                (*check if there is a better way to do*)

let isPositive x = x>=0;;                                             
                                            
let _float_without_minus_zero = 
    let parse = (caten _integer_ (caten (char_ci '.') _natural_)) in
    pack parse (fun (i , (x,n)) -> match i with
                                            |Number(Int(i_cont))-> Number(Float(float_of_string ((string_of_int i_cont) ^ "." ^  (list_to_string n))))
                                            | _ -> raise X_no_match);;

let _float_with_minus_zero = 
    let parse = (caten (word "-0") (caten (char_ci '.') _natural_)) in
    pack parse (fun (i , (x,n)) -> Number(Float(float_of_string("-0." ^ (list_to_string n)))));;
    
let _float_ = (disj _float_with_minus_zero _float_without_minus_zero);;
                                            
let _hex_float_without_minus_zero = 
    let parse = (caten _hex_integer_ (caten (char_ci '.') _hex_natural_)) in                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 
    pack parse (fun (i , (x,n)) -> match i with
                                            |Number(Int(i_cont)) -> if (isPositive i_cont) 
                                                                                then Number(Float(((float_of_int i_cont) +. (float_of_string ("0x0." ^ (list_to_string n))))))
                                                                                else Number(Float(((float_of_int i_cont) -. (float_of_string ("0x0." ^ (list_to_string n))))))
                                            | _ -> raise X_no_match);;

let _hex_float_with_minus_zero = 
    let parse = (caten (word_ci "#x-0") (caten (char_ci '.') _hex_natural_)) in                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 
    pack parse (fun (i , (x,n)) -> Number(Float(-1.0 *. float_of_string ("0x0." ^ (list_to_string n)))));; 
    
let _hex_float_ = (disj _hex_float_with_minus_zero _hex_float_without_minus_zero);;
                            
let isPositive x = x>0;;                                             

(* /---------------------------String sub parsers -----------------------/ *)

(* Parser for StringLiteralChar:*)

let backslash = '\\';; 
let dqoute = '\"';;

let _string_literal_char_ = 
    let parse = const(fun(c) -> c <> backslash && c <> dqoute) in 
    pack parse (fun (c) -> c);;

(* Parser for StringMetaChar: *)

let metaChar_list = List.map word_ci ["\\r"; "\\n"; "\\t"; "\\f"; "\\\\"; "\\\""];;

let _string_meta_char_ = 
    let parse = disj_list metaChar_list in 
    pack parse (fun(ls) -> match (list_to_string(List.map lowercase_ascii ls)) with
                                    | "\\r" -> Char.chr(13)
                                    | "\\n" -> Char.chr(10)
                                    | "\\t" -> Char.chr(9)
                                    | "\\f" -> Char.chr(12)
                                    | "\\\\" -> Char.chr(92)
                                    | "\\\"" -> Char.chr(34)
                                    | _ -> Char.chr(0));;
                                    
(* Parser for StringHexChar: *)

let _string_hex_char_ = 
    let parse = caten (caten (word_ci "\\x") (plus _hex_digit_)) (char ';') in
    pack parse (fun ((prefix, n), eoi) -> Char.chr(int_of_string("0x" ^ (list_to_string n))));;
    
(* Parser for StringChar: *)

let _string_char_ = disj_list [_string_meta_char_;_string_literal_char_;_string_hex_char_];;


(* /---------------------------Symbol sub parsers -----------------------/ *)

(* Parser for SymbolChar: *)

let alphabet = range 'a' 'z';;
let alphabetCAPS = range 'A' 'Z';;
let _symbol_char_ = disj_list [_digit_;alphabet; alphabetCAPS; char '!' ; char '$'; char '^'; char '*' ;char '-' ;char '_' ;char '='; char '+'; char '<'; char '>'; char '?'; char '/'; char ':'];;


(* /---------------------------List Family sub parsers & helper functions -----------------------/ *)
let rec _nested_pair s_list = match s_list with 
                            | [] -> Nil
                            | head :: tail -> Pair(head, (_nested_pair tail));;
                            
let rec _nested_pair_dlst s_lst tl = match s_lst with 
                                    | [] -> tl
                                    | head :: tail -> Pair(head, (_nested_pair_dlst tail tl));;


(* /----------------------------------Parser for sexpr: ----------------------/ *)
                                
let rec _sexpr_ s = 

    let parser_lst = [_auto_paren_balance_ ; _scientific_notation_; _bool_; _char_ ;_number_;_string_; _symbol_; _dotted_list_ ;_list_; _bracket_notation_ ; _vector_; _qoute_; _quasi_qoute_; _unqouted_; _unqoute_and_spliced_] in
  
    let trimmed_parser_lst = List.map _trim_ parser_lst in
    
    let _parser_ = disj_list trimmed_parser_lst in 
    _parser_ s
    
    (* Parser for Boolean: *)

    and _bool_ s = 
        let parse = disj (word_ci "#t") (word_ci "#f") in
        let _packed_ = pack parse (fun (b) -> if (list_to_string (List.map lowercase_ascii b)) = "#f" then Bool(false) else Bool(true))in 
        _packed_ s
    
    (* Parser for comments :*)
    and _lparen_ s = 
        let _lp_ = char '(' in
        let _packed_ = pack _lp_ (fun(p)-> Char(p)) in
        let _spaced_ = _trim_ _packed_ in
        _spaced_ s

    and _rparen_ s = 
        let _rp_ = char ')' in 
        let _packed_ = pack _rp_ (fun(p)-> Char(p)) in
        let _spaced_ = _trim_ _packed_ in
        _packed_ s
    
    and _lbracket_ s = 
        let _lb_ = char '[' in 
        let _packed_ = pack _lb_ (fun(b)-> Char(b)) in
        let _spaced_ = _trim_ _packed_ in
        _packed_ s
    
    and _rbracket_ s = 
        let _rb_ = char ']' in 
        let _packed_ = pack _rb_ (fun(b)-> Char(b)) in
        let _spaced_ = _trim_ _packed_ in
        _packed_ s
    
    and _comments_ s = 
        let comment_prefix = char ';' in
        let newline = char_ci '\n' in 
        let comment_char = diff nt_any newline in 
        let comment = star comment_char in
        let packed_eoi = pack nt_end_of_input (fun(ch) -> '\000') in
        let end_of_comment = disj packed_eoi newline in 
        let parse = caten (caten comment_prefix comment) end_of_comment in 
        let _packed_ = pack parse (fun ((pre, body), e) -> pre) in 
        _packed_ s
    
    and _comments_sexpr s = 
        let sexpr_comment_prefix = word "#;" in
        let parse = caten sexpr_comment_prefix _sexpr_ in
        let _packed_ = pack parse (fun(ch) -> '\000') in 
        _packed_ s

    and _trim_ par s = 
        let delimiter_and_comment = disj_list [nt_whitespace;_comments_; _comments_sexpr] in
        let textual_data = star delimiter_and_comment in 
        let parse = caten (caten textual_data par) textual_data in 
        let _packed_ = pack parse (fun((l, p), r) -> p) in
        _packed_ s

    (* Parser for Char: *)
        
    and _char_ s = 
        let parse = caten _char_prefix_ (disj_list [_hex_char_;_named_char_;_visible_simple_char]) in
        let _packed_ = pack parse (fun (prefix, ch) -> ch) in 
        _packed_ s
    
    and _number_ s = 
        let parse = (disj_list [_float_;_hex_float_;_integer_ ; _hex_integer_ ]) in
        let _packed_ = pack parse (fun(x) -> x) in 
        _packed_ s
    
    (*Parser for String :*)

    and _string_ s = 
        let parse = caten (caten (char dqoute) (star _string_char_)) (char dqoute) in 
        let  _packed_ = pack parse (fun((lq, ch_lst), rq) -> String(list_to_string ch_lst)) in 
        _packed_ s
        
    (*Parser for Symbol: *)

    and _symbol_ s = 
        let parse = plus _symbol_char_ in 
        let _packed_ = pack parse (fun(ls) -> Symbol (list_to_string(List.map lowercase_ascii ls))) in 
        _packed_ s
    
    (* Parser for list : *)
    
    and _list_ s = 
        let parse = caten (caten ( _lparen_) (star (_sexpr_))) (_rparen_) in 
        let _packed_ = pack parse (fun ((lp,s_lst),rp) -> (_nested_pair s_lst)) in 
        _packed_ s
     
    (* Parser for dotted list : *)
    
    and _dotted_list_ s = 
        let dot = (char '.') in
        let parse = caten (caten (caten (caten ( _lparen_) (plus(_sexpr_))) (dot) ) (_sexpr_)) ( _rparen_) in
        let _packed_ = pack parse (fun((((lp,s_lst),d),tl),rp)-> (_nested_pair_dlst s_lst tl)) in 
        _packed_ s
    
    (* Parser for vector: *)
    
    and _vector_ s = 
        let pound = char '#' in 
        let parse = caten (caten (caten ( pound) ( _lparen_)) (star (_sexpr_))) ( _rparen_ )  in
        let _packed_ = pack parse (fun(((pound,lp),lst),rp) -> Vector(lst)) in
        _packed_ s
    
    (* Parser for qoute : *)
    
    and _qoute_ s = 
        let qoute = char '\'' in
        let parse = caten qoute _sexpr_ in 
        let _packed_ = pack parse (fun (q,e) -> Pair(Symbol("quote"), Pair(e, Nil))) in 
        _packed_ s
    
    (* Parser for quasi qoute : *)
    
    and _quasi_qoute_ s =
        let qqoute = char '`' in 
        let parse = caten qqoute _sexpr_ in 
        let _packed_ = pack parse (fun (q,e) -> Pair(Symbol("quasiquote"), Pair(e, Nil))) in 
        _packed_ s
    
    (* Parser for unqouted : *)
        
    and _unqouted_ s =
        let comma = char ',' in 
        let parse = caten comma _sexpr_ in 
        let _packed_ = pack parse (fun (q,e) -> Pair(Symbol("unquote"), Pair(e, Nil))) in 
        _packed_ s
        
    (* Parser for unqouted and spliced : *)
        
    and _unqoute_and_spliced_ s =
        let us = word_ci ",@" in 
        let parse = caten us _sexpr_ in 
        let _packed_ = pack parse (fun (us,e) -> Pair(Symbol("unquote-splicing"), Pair(e, Nil))) in 
        _packed_ s
    
    (* Parser for sientific notation : *)
        
    and _scientific_notation_ s =
        let parse = (not_followed_by (caten (caten (disj _float_ _integer_) (char_ci 'e')) _integer_) nt_any) in
        let _packed_ = pack parse (fun ((first,e) , second) -> match first , second with
                                                                |Number(Float(f_cont)) , Number(Int(s_cont)) -> Number(Float(f_cont *. (10.0 ** float_of_int(s_cont))))
                                                                |Number(Int(f_cont)) , Number(Int(s_cont)) -> Number(Float(float_of_int(f_cont) *. (10.0 ** float_of_int(s_cont))))
                                                                | _ -> raise X_no_match) in 
                                                                _packed_ s
    
    (* Parser for bracket notation: *)
    and _list_bracket_notation s =
        let parse = (caten (caten (_lbracket_) (star _sexpr_)) (_rbracket_)) in
        let _packed_ = pack parse (fun ((b1 , x), b2) -> _nested_pair x) in
        _packed_ s
    
    and _dotted_list_bracket_notation s = 
        let parse = (caten (caten (caten (caten (_lbracket_) (plus _sexpr_)) (char '.')) _sexpr_) (_rbracket_)) in
        let _packed_ = pack parse (fun ((((b1 , xplus), dot), x), b2) -> _nested_pair_dlst xplus x) in
        _packed_ s
        
    and _bracket_notation_ s = 
        let parse = (disj _list_bracket_notation _dotted_list_bracket_notation) in
        let _packed_ = pack parse (fun (x) -> x) in
        _packed_ s
        
    (* Parser for 3-dot :*)
    and _auto_paren_balance_ s = 
        let _auto_balance_ = (word "...") in
        let parse = (caten (disj_list [_open_dotted_list_ ; _open_list_ ; _open_vector_]) _auto_balance_) in
        let _packed_ = pack parse (fun (x, dots) -> x) in
        _packed_ s
    
    and _reg_sexpr_ s= 
        let parse = (disj_list [(diff _sexpr_ _auto_paren_balance_) ; _open_dotted_list_; _open_list_  ; _open_vector_]) in 
        let _packed_ = (pack parse (fun (x)->x)) in
        _packed_ s
        
    and _open_list_ s = 
        let parse_p = (caten _lparen_ (caten (star _reg_sexpr_) (maybe _rparen_))) in
        let parse_b = (caten _lbracket_ (caten (star _reg_sexpr_) (maybe _rbracket_))) in
        let parse = disj parse_b parse_p in
        let _packed_ = (pack parse (fun (lp , (x , rp)) -> (_nested_pair x))) in
        _packed_ s
    
    and _open_dotted_list_ s = 
        let parse_p = (caten (caten (caten (caten _lparen_ (plus _reg_sexpr_)) (char '.')) _reg_sexpr_) (maybe _rparen_)) in
        let parse_b = (caten (caten (caten (caten _lbracket_ (plus _reg_sexpr_)) (char '.')) _reg_sexpr_) (maybe _rbracket_)) in
        let parse = disj parse_b parse_p in
        let _packed_ = (pack parse (fun ((((lp, xplus),dot),x),rp) -> (_nested_pair_dlst xplus x))) in
        _packed_ s
        
    and _open_vector_ s= 
        let parse_p = (caten (caten (caten (char '#') _lparen_) (star _reg_sexpr_)) (maybe _rparen_)) in
        let parse_b = (caten (caten (caten (char '#') _lbracket_) (star _reg_sexpr_)) (maybe _rbracket_)) in
        let parse = disj parse_b parse_p in
        let _packed_ = pack parse (fun (((ht , lp) , x ), rp) -> Vector(x)) in
        _packed_ s ;;  

                                                            
let read_sexpr string = 
    let (sexpr, char_lst) = (not_followed_by _sexpr_ nt_any) (string_to_list string) in
    sexpr;;

let read_sexprs string = if string = "" then [] 
                                        else let (sexprs, char_lst) = (star _sexpr_) (string_to_list string) in 
    sexprs;;

end;; (* struct Reader *)

