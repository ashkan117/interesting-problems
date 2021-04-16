(* 
 * Source of inspiration 
 * https://github.com/zhehaowang/ucla-cs131/blob/master/hw2/hw2.ml *)

let accept_all derivation string = Some (derivation, string)
let accept_empty_suffix derivation = function
   | [] -> Some (derivation, [])
   | _ -> None

type ('nonterminal, 'terminal) symbol =
  | N of 'nonterminal
  | T of 'terminal

type awksub_nonterminals =
  | Expr | Term | Lvalue | Incrop | Binop | Num

let awkish_grammar =
  (Expr,
   function
     | Expr ->
         (* [[T"$"; T"1"; T"++"; T"-"; T"2"]; *)
         [[N Term; N Binop; N Expr];
          [N Term]]
     | Term ->
         [[N Num];
    [N Lvalue];
    [N Incrop; N Lvalue];
    [N Lvalue; N Incrop];
    [T"("; N Expr; T")"]]
     | Lvalue ->
         [[T"$"; N Expr]]
     | Incrop ->
         [[T"++"];
    [T"--"]]
     | Binop ->
         [[T"+"];
    [T"-"]]
     | Num ->
         [[T"0"]; [T"1"]; [T"2"]; [T"3"]; [T"4"];
    [T"5"]; [T"6"]; [T"7"]; [T"8"]; [T"9"]])

let small_awk_frag = ["$"; "1"; "++"; "-"; "2"]

let match_empty frag accept = accept frag
let match_nothing frag accept = None
let match_value term frag accept =
  match frag with
    | [] -> None
    | n::tail -> if n = term then accept tail else None

(* Add paranthesis to give order to nested matches *)
let rec make_appended_matchers get_rules rule acceptor derivation frag = 
  match rule with 
    | [] -> acceptor derivation frag
    | (T terminal)::rule_tail -> 
        (match frag with 
        | [] -> None
        | frag_head :: frag_tail -> 
            if (frag_head = terminal) 
            then make_appended_matchers get_rules rule_tail acceptor derivation frag_tail
            else None)
    | (N nonterminal)::rule_tail -> 
        let newAcceptor = make_appended_matchers get_rules rule_tail acceptor
        in make_or_matchers get_rules (get_rules nonterminal) nonterminal newAcceptor frag derivation
and make_or_matchers get_rules matching_rules lhs acceptor frag derivation = 
  match matching_rules with
    | [] -> None
    | rules_head :: rules_tail -> 
        let result =  make_appended_matchers get_rules rules_head acceptor ( derivation@[(lhs,rules_head)]) frag 
        in match result with  
        | None -> make_or_matchers get_rules rules_tail lhs acceptor frag derivation
        | _ -> result 
      

let get_rules = (snd awkish_grammar) 
let start = (fst awkish_grammar)

let make_matcher (start_symbol,get_rules) acceptor frag = 
  make_or_matchers get_rules (get_rules start_symbol) start_symbol acceptor frag []

