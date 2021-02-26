(* Ce mini-projet porte sur l'apprentissage d'automates séparateurs.
   La lecture de la Section 16.3 des notes de cours est fortement
   recommandée. Le code que vous devez écrire prend en entrée deux
   listes de mots I et E, lues à partir d'un fichier passé en argument
   et renvoie sur la sortie standard le code SMT-LIB à faire passer
   dans une solveur SMT, comme Z3. 
 *)

open Printf

(* ensembles de test : ensemble I *)
let li = ["";"ab"]
             
(* ensembles de test : ensemble E *)
let le = ["aa";"b"]


(* ======================================================================= *)
(* EXERCICE 1 : extraire  l'alphabet de l'automate.
   La fonction alphabet_from_list prend en entrée une liste de
   chaînes de caractères et retourne une liste triée de
   caractères sans duplication. 
 *)
(* explode : string -> char list 
   prend une chaîne de caractères et renvoie la liste de ses caractères 
 *)
let explode (s: string) : char list =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

(*  add_list : 'a list -> 'a list -> 'a list 
 *  concatène deux listes de manière récursive terminale
 *)
let add_list (list1 : 'a list) (list2 : 'a list) : 'a list =
  let rec add_aux list1 list2 accu = 
    match list1, list2 with 
    | [],[] -> accu
    | [],h::t -> add_aux [] t (h::accu)
    | h::t,l-> add_aux t l (h::accu)
  in List.rev (add_aux list1 list2 []);;    (* le fait d'être récursive terminale inverse la liste *)

(* alphabet_from_list : string list -> char list  
   - prend en entrée une liste l de chaînes de caractères 
   - renvoie la liste triée et sans duplication de caractères
     apparaissant dans l
 *)
let alphabet_from_list (l : string list) : char list =
  let rec aux acc = function
      | h::q -> aux (add_list (explode h) acc) q  (* on décompose en char list la string h *)
      | [] -> acc                                 
  in let list_c = aux [] l in
  List.sort_uniq (Char.compare) list_c    (* List.sort_uniq trie et retire les éventuels doublons*)
;;
  
(* test *)
(* let a = alphabet_from_list (li @ le) *)

(* ======================================================================= *)
(* EXERCICE 2 : définition de l'alphabet A et de l'arbre préfixe T en
   SMT-LIB Pour les listes données en exemple, la sortie de la
   fonction declare_types doit être la chaîne de caractères
   "(declare-datatypes () ((A a b) (T e ea eaa eab eb)))" *)

(* prefixes : string -> string list
   renvoie la liste des préfixes d'une chaîne de caractères 
   Nous allons ajouter à chaque préfixe le caractère 'e'.
   Par exemple, prefixes "aba" = ["e"; "ea"; "eab"; "eaba"]
   -> pour ce faire, on utilise String.sub en enlevant progressivement les char de s en fin de chaîne
    *)
let prefixes (s : string) : string list =
  let rec aux i acc =
    let pref_i = String.sub s 0 i in (* Découpage de la chaîne *)
    if i > 0 then aux (i-1) (("e"^pref_i )::acc) else ("e"::acc) (* Ajoute "e" au début de chaque préfixe *)
  in
  aux (String.length s) []
;;

  
(* prefixes_of_list : string list -> string list
   renvoie la liste triée et sans doublons des préfixes des chaînes 
   de caractères d'une liste donnée *)
let prefixes_of_list (l : string list) : string list = 
  let rec aux acc = function
      | h::q ->
        let pref_list = prefixes h in       (* on récupère les préfixes de chaque string auquel on a ajouter le char 'e' au début *)
        aux (add_list (pref_list) acc) q
      | [] -> acc
  in
  let liste_s = aux [] l in
  List.sort_uniq (String.compare) liste_s   (* List.sort_uniq trie et enlève les doublons *)
;;
  
(* declare_types_alphabet : char list -> string
   prend une liste de caractères [c_1; ...; c_n] et renvoie une chaîne 
   de la forme "(A c_1... c_n)" *)
let declare_types_alphabet (cl : char list) : string =
    let rec aux ret = function
        | h::q -> aux (ret^" "^(Char.escaped h)) q (* Char.escaped convertit un char en string pour la concaténation*)
        | [] -> ret^")"
    in aux "(A" cl
;;

(* declare_types_trie : string list -> string 
   prend une liste l de chaînes de caractères et 
   renvoie une chaîne de la forme "(T es_1 ... es_n)" où 
   s_1... s_n est une énumération de tous les 
   prefixes des chaînes apparaissant dans l *)
let declare_types_trie (l : string list) : string =
  let pref_liste = prefixes_of_list l in
  let rec aux ret = function
      | h::q -> aux (ret^" "^h) q
      | [] -> ret^")"
  in aux "(T" pref_liste
;;

(* declare_types : string list -> char list -> string *)  
let declare_types (l : string list) (cl : char list) : string =
  let ret = "; définition de l'alphabet A et de l'arbre préfixe T\n(declare-datatypes () (" in
  ret^(declare_types_alphabet cl)^" "^(declare_types_trie l )^"))"
;;
  
(* test *)
(* Printf.printf "%s" (declare_types (li @ le) a) *)
  

(* ======================================================================= *)
(* EXERCICE 3 : définir une chaîne de caractères pour les définitions
   en SMT-LIB de
   - l'ensemble d'états Q,
   - la fonction delta de transition de l'automate,
   - l'ensemble final des états acceptants et
   - la fonction f,
   ainsi que les assertions associées.
   Ces définitions ne dépendent pas des listes de mots acceptés ou rejetés. *)

let define_sorts_and_functions : string  =
"
; les états de l'automate à trouver sont {0, 1, ..., n-1}
(define-sort Q () Int)
(declare-const n Q)
(assert (> n 0))\n

; fonction de transition de l'automate
(declare-fun delta (Q A) Q)
(assert (forall ((q Q) (a A))
(and (>= (delta q a) 0) (< (delta q a) n))))\n

; ensemble d'états acceptants de l'automate
(declare-fun final (Q) Bool)

; fonction des éléments de l'arbre préfixe vers les états
(declare-fun f (T) Q)
(assert (forall ((x T))
(and (>= (f x) 0) (< (f x) n))))\n

; contrainte sur l'état initial, donnée par l'équation (55)
; dans la section 16.3 des notes de cours
(assert (= 0 (f e)))\n
"
  ;;
  
(* ======================================================================= *)
(* EXERCICE 4 : contraintes sur les transitions
   La fonction assert_transition_constraints prend en entrée une trie 
   et retourne une chaîne qui modélise les contraintes sur les transitions 
   de l'automate décrites par la formule (56). *)
  
(* eq_trans_constr : string -> char -> string
   renvoie une chaîne de caractères qui correspond à une formule atomique pour 
   la transition étiquetée avec 'a' à partir de l'état s
   Par exemple, pour s = "abc" et  c = 'd' on a 
   eq_trans_constr outputs "(= (f abcd)  (delta (f abc)  d))" *)
let eq_trans_constr (s : string) (a : char) : string =
  let c = Char.escaped a in (* Char.escaped convertie le char 'a' en string pour la concaténation *)
  "eq_trans_constr outputs \"(= (f "^s^c^")  (delta (f "^s^")  "^c^"))\""
;;

(* list_transition_constraints : string list -> string list
   prend une liste de chaînes de caractères et génère une liste 
   de formules atomiques ou de chaînes vides comme suit
   - pour une chaîne non vide de la forme sa on obtient
     une chaine correspondant à l'équation f(sa) = delta (fs) a
   - pour la chaîne vide on obtient la chaîne vide *)
let list_transition_constraints (l : string list) : string list =
  let rec aux acc = function
      | h :: q ->
        if h = "" || h = "e" then aux acc q
        else
          let len = String.length h in
          let first = String.sub h 0 (len-1) in
          let last = String.sub h (len-1) 1 in
          aux (("(f "^h^") (delta (f "^first^") "^last^")")::acc) q
      | [] -> acc
    in aux [] l
;;
  
(* compare_length : string -> string -> int
   prend 2 string et compare leur tailles respectives sinon utilise l'ordre lexicographique *)  
(* ATTENTION: Cette fonction est finalement inutilisé mais elle permettait de trier dans l'ordre,
   les mots dans la chaine qui modélise les contraintes sur les transitions de l'automate décrit par la 
   formule (56) lors de l'affichage du résultat *)
let compare_length (s1 : string) (s2 : string) : int =
  if String.length s1 > String.length s2 then -1        
  else if String.length s1 < String.length s2 then 1    
  else (String.compare s2 s1)                           
;;

(* assert_transition_constraints : string list -> string
   prend en entrée une liste de mots et renvoie une chaîne qui modélise 
   les contraintes sur les transitions de l'automate décrit par la 
   formule (56).
   Par exemple, pour la liste [""; "ab"; "aa"; "b"] on obtient la chaîne
   "(assert (and 
               (= (f ea)  (delta (f e)  a))
               (= (f eaa)  (delta (f ea)  a))
               (= (f eab)  (delta (f ea)  b))
               (= (f eb)  (delta (f e)  b))))"
 *)
let assert_transition_constraints (l : string list) : string =
  let rec aux ret = function
      | h::q -> aux ("          (= "^h^")\n"^ret) q
      | [] -> ("; contrainte sur les transitions, donnée par l'équation (56)\n(assert (and \n"^ret)
  in
  let liste = list_transition_constraints (prefixes_of_list l) in
  aux "))" (liste)
;;

(* test *)
(* Printf.printf "%s" (assert_transition_constraints (li @ le)) *)

(* ======================================================================= *)
(* EXERCICE 5 : contraintes sur les états acceptants La fonction
   assert_acceptance prend en entrée deux listes de mots et retourne
   une chaîne de caractères qui modélise les contraintes sur les états
   acceptants décrites par la formule (57). *)

(* eq_accept : string -> string 
   - prend une chaîne de caractères s et renvoie une chaîne de caractères 
   qui modélise l'appartenance de s à l'ensemble final des états acceptants *)
let eq_accept (s : string) : string =
  "(final (f e"^s^"))"
;;

(* eq_non_accept : string -> string 
   - prend une chaîne de caractères s et renvoie une chaîne de caractères 
   qui modélise la non-appartenance de s à l'ensemble final des états acceptants 
 *)
let eq_non_accept (s : string) : string =
  "(not(final (f e"^s^")))"
;;

(* assert_acceptance : string list -> string list > string
   prend deux listes de chaînes de caractères, li et le, et renvoie une
   chaine qui modélise les contraintes sur les états acceptants
   décrites par la formule (52). 
   Les mots dans li sont acceptés et les mots dans le ne le sont pas. *)
let assert_acceptance (li : string list) (le : string list) : string  =
  let rec aux acc fonct = function
      | h::q -> aux ((fonct h)^"\n                "^acc) fonct q
      | [] -> acc
  in
  let fin = aux "))" eq_non_accept le in
  let milieu = aux fin eq_accept (li) in
  "; contrainte sur les états finaux, donnée par l'équation (57)\n(assert (and  "^milieu
;;
  
(* test *)
(* Printf.printf "%s" (assert_acceptance li le) *)
  
(* ======================================================================= *)
(* EXERCICE 6 :
   La fonction smt_code prend en entrée deux listes de mots
   et retourne une chaîne de caractères qui donne l'implémentation 
   en SMT-LIB. *)

(* smt_code : string list -> string list -> string 
   prend deux listes de chaînes de caractères, li et le, et renvoie une chaîne 
   de caractères qui donne l'implémentation en SMT-LIB.
   Les mots dans li sont acceptés et les mots dans le ne le sont pas. 
   Pour vérifier votre algorithme, vous pouvez essayer le code SMT-LIB 
   que vous obtenez dans le solveur Z3: https://rise4fun.com/z3 *)
let smt_code (li : string list) (le : string list) : string =
  let l = add_list li le in
  let cl = alphabet_from_list (l) in
  (declare_types l cl)^"\n"^
  define_sorts_and_functions^"\n"^
  (assert_transition_constraints (l))^"\n"^
  (assert_acceptance li le)^"\n"^
  "(check-sat-using (then qe smt))
(get-model)
(exit)"
;;

(* test *)
(* Printf.printf "%s" (smt_code li le) *)


(* ======================================================================= *)
(* lire deux listes de chaîne de caractères I et E d'un fichier *)
(* Ne pas modifier cette partie *)

let input_line_opt ic =
  try Some (input_line ic)
  with End_of_file -> None
                    
let read_lines ic =
  let rec aux acc =
    match input_line_opt ic with
    | Some line -> aux (line::acc)
    | None -> (List.rev acc)
  in
  aux []
  
let lines_of_file filename =
  let ic = open_in filename in
  let lines = read_lines ic in
  close_in ic;
  (lines)

let read_lists_from_file (filename: string): ((string list) * (string list))  =
  let lines = lines_of_file filename in
  (String.split_on_char ' ' (List.nth lines 0),
   String.split_on_char ' ' (List.nth lines 1))
  
let () =
  let (li,le) = (read_lists_from_file Sys.argv.(1)) in
  let output_file = open_out "output.smtlib" in
  let res = smt_code li le in 
  Printf.printf "%s" res; output_string output_file res;;