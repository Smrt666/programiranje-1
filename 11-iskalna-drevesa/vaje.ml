(* ========== Vaja 4: Iskalna Drevesa  ========== *)

(*-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=*]
 Ocaml omogoča enostavno delo z drevesi. Konstruiramo nov tip dreves, ki so
 bodisi prazna, bodisi pa vsebujejo podatek in imajo dve (morda prazni)
 poddrevesi. Na tej točki ne predpostavljamo ničesar drugega o obliki dreves.
[*-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=*)

type 'a tree = 
  | Empty
  | Node of 'a * 'a tree * 'a tree

(*----------------------------------------------------------------------------*]
 Definirajmo si testni primer za preizkušanje funkcij v nadaljevanju. Testni
 primer predstavlja spodaj narisano drevo, pomagamo pa si s pomožno funkcijo
 [leaf], ki iz podatka zgradi list.
          5
         / \
        2   7
       /   / \
      0   6   11
[*----------------------------------------------------------------------------*)

let leaf x = Node(x, Empty, Empty)

let test_tree = Node (5, Node (2, leaf 0, Empty), Node (7, leaf 6, leaf 11))

(*----------------------------------------------------------------------------*]
 Funkcija [mirror] vrne prezrcaljeno drevo. Na primeru [test_tree] torej vrne
          5
         / \
        7   2
       / \   \
      11  6   0
 - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 # mirror test_tree ;;
 - : int tree =
 Node (Node (Node (Empty, 11, Empty), 7, Node (Empty, 6, Empty)), 5,
 Node (Empty, 2, Node (Empty, 0, Empty)))
[*----------------------------------------------------------------------------*)

let mirror t =
  let rec a t =
    match t with
    | Empty -> Empty
    | Node(x, l, r) -> Node(x, a r, a l)
  in
  a t

let mt = mirror test_tree
;; assert (mt = Node (5, Node (7, leaf 11, leaf 6), Node (2, Empty, leaf 0)))


(*----------------------------------------------------------------------------*]
 Funkcija [height] vrne višino oz. globino drevesa, funkcija [size] pa število
 vseh vozlišč drevesa.
 - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 # height test_tree;;
 - : int = 3
 # size test_tree;;
 - : int = 6
[*----------------------------------------------------------------------------*)
let height t = 
  let rec a t =
    match t with
    | Empty -> 0
    | Node(_, l, r) -> 1 + max (a l) (a r)
  in
  a t

let size t =
  let rec a t =
    match t with
    | Empty -> 0
    | Node(_, l, r) -> 1 + a l + a r
  in
  a t

;; assert (height test_tree = 3)
;; assert (height (leaf 1) = 1)
;; assert (height Empty = 0)

;; assert (size test_tree = 6)
;; assert (size (leaf 1) = 1)
;; assert (size Empty = 0)

(*----------------------------------------------------------------------------*]
 Funkcija [map_tree f tree] preslika drevo v novo drevo, ki vsebuje podatke
 drevesa [tree] preslikane s funkcijo [f].
 - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 # map_tree ((<)3) test_tree;;
 - : bool tree =
 Node (Node (Node (Empty, false, Empty), false, Empty), true,
 Node (Node (Empty, true, Empty), true, Node (Empty, true, Empty)))
[*----------------------------------------------------------------------------*)

let map_tree f t =
  let rec a t =
    match t with
    | Empty -> Empty
    | Node(x, l, r) -> Node(f x, a l, a r)
  in
  a t

;; assert (map_tree ((<)3) test_tree = Node (true, Node (false, Node (false, Empty, Empty), Empty), Node (true, Node (true, Empty, Empty), Node (true, Empty, Empty))))



(*----------------------------------------------------------------------------*]
 Funkcija [list_of_tree] pretvori drevo v seznam. Vrstni red podatkov v seznamu
 naj bo takšen, da v primeru binarnega iskalnega drevesa vrne urejen seznam.
 - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 # list_of_tree test_tree;;
 - : int list = [0; 2; 5; 6; 7; 11]
[*----------------------------------------------------------------------------*)

let list_of_tree t =
  let rec a t =
    match t with
    | Empty -> []
    | Node(x, l, r) -> (a l) @ [x] @ (a r)
  in
  a t

;; assert (list_of_tree test_tree = [0; 2; 5; 6; 7; 11])

(*----------------------------------------------------------------------------*]
 Funkcija [is_bst] preveri ali je drevo binarno iskalno drevo (Binary Search 
 Tree, na kratko BST). Predpostavite, da v drevesu ni ponovitev elementov, 
 torej drevo npr. ni oblike Node( leaf 1, 1, leaf 2)). Prazno drevo je BST.
 - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 # is_bst test_tree;;
 - : bool = true
 # test_tree |> mirror |> is_bst;;
 - : bool = false
[*----------------------------------------------------------------------------*)

let is_bst t =
  let rec a t =
    match t with
    | Empty -> (true, None, None)
    | Node(x, l, r) ->
      let (bl, lmin, lmax) = a l in
      let (br, rmin, rmax) = a r in
      if bl && br then
        match lmax, rmin with
        | None, None -> (true, Some x, Some x)
        | None, Some rm -> if x < rm then (true, Some x, rmax) else (false, None, None)
        | Some lm, None -> if lm < x then (true, lmin, Some x) else (false, None, None)
        | Some lm, Some rm -> if lm < x && x < rm then (true, lmin, rmax) else (false, None, None)
      else
        (false, None, None)
  in
  let (b, _, _) = a t in b

;; assert (is_bst test_tree = true)
;; assert (is_bst Empty = true)
;; assert (is_bst (leaf 5) = true)
;; assert (is_bst (Node (4, Empty, leaf 5)) = true)
;; assert (is_bst (Node (5, leaf 5, Empty)) = false)
;; assert (test_tree |> mirror |> is_bst = false)

(*-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=*]
 V nadaljevanju predpostavljamo, da imajo dvojiška drevesa strukturo BST.
[*-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=*)

(*----------------------------------------------------------------------------*]
 Funkcija [insert] v iskalno drevo pravilno vstavi dani element. Funkcija 
 [member] preveri ali je dani element v iskalnem drevesu.
 - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 # insert 2 (leaf 4);;
 - : int tree = Node (Node (Empty, 2, Empty), 4, Empty)
 # member 3 test_tree;;
 - : bool = false
[*----------------------------------------------------------------------------*)

let rec member x t =
  match t with
  | Empty -> false
  | Node(y, l, r) -> if x = y then true else if x < y then member x l else member x r

let rec insert x t =
  match t with
  | Empty -> leaf x
  | Node(y, l, r) ->
    if x = y then t
    else if x < y then Node(y, insert x l, r)
    else Node(y, l, insert x r)

;; assert (insert 2 (leaf 4) = Node (4, Node (2, Empty, Empty), Empty))
;; assert (member 3 test_tree = false)

(*----------------------------------------------------------------------------*]
 Funkcija [member2] ne privzame, da je drevo bst.
 
 Opomba: Premislte kolikšna je časovna zahtevnost funkcije [member] in kolikšna
 funkcije [member2] na drevesu z n vozlišči, ki ima globino log(n). 
[*----------------------------------------------------------------------------*)

let rec member2 x t =
  match t with
  | Empty -> false
  | Node(y, l, r) -> if x = y then true else member2 x l || member2 x r

(*----------------------------------------------------------------------------*]
 Funkcija [succ] vrne naslednjika korena danega drevesa, če obstaja. Za drevo
 oblike [bst = Node(l, x, r)] vrne najmanjši element drevesa [bst], ki je večji
 od korena [x].
 Funkcija [pred] simetrično vrne največji element drevesa, ki je manjši od
 korena, če obstaja.
 - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 # succ test_tree;;
 - : int option = Some 6
 # pred (Node(Empty, 5, leaf 7));;
 - : int option = None
[*----------------------------------------------------------------------------*)

let rec min_tree t =
  match t with
  | Empty -> None
  | Node(x, Empty, _) -> Some x
  | Node(_, l, _) -> min_tree l

let rec max_tree t =
  match t with
  | Empty -> None
  | Node(x, _, Empty) -> Some x
  | Node(_, _, r) -> max_tree r

let succ t =
  match t with
  | Empty -> None
  | Node(_, _, r) -> min_tree r

let pred t =
  match t with
  | Empty -> None
  | Node(_, l, _) -> max_tree l

;; assert (succ test_tree = Some 6)
;; assert (pred (Node(5, Empty, leaf 7)) = None)
;; assert (succ (Node(5, Empty, leaf 7)) = Some 7)



(*----------------------------------------------------------------------------*]
 Na predavanjih ste omenili dva načina brisanja elementov iz drevesa. Prvi 
 uporablja [succ], drugi pa [pred]. Funkcija [delete x bst] iz drevesa [bst] 
 izbriše element [x], če ta v drevesu obstaja. Za vajo lahko implementirate
 oba načina brisanja elementov.
 - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 # (*<< Za [delete] definiran s funkcijo [succ]. >>*)
 # delete 7 test_tree;;
 - : int tree =
 Node (Node (Node (Empty, 0, Empty), 2, Empty), 5,
 Node (Node (Empty, 6, Empty), 11, Empty))
[*----------------------------------------------------------------------------*)

let rec delete x t =
  match t with
  | Empty -> Empty
  | Node(y, l, r) ->
    if x < y then Node(y, delete x l, r)
    else if x > y then Node(y, l, delete x r)
    else
      match succ t with
      | None -> l
      | Some s -> Node(s, l, delete s r)

;; assert (delete 7 test_tree = Node (5, Node (2, Node (0, Empty, Empty), Empty), Node (11, Node (6, Empty, Empty), Empty)))
;; assert (delete 1 (leaf 2) = leaf 2)
;; assert (delete 2 (leaf 2) = Empty)
;; assert (delete 5 test_tree = Node (6, Node (2, leaf 0, Empty), Node (7, Empty, leaf 11)))

(*-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=*]
 SLOVARJI

 S pomočjo BST lahko (zadovoljivo) učinkovito definiramo slovarje. V praksi se
 slovarje definira s pomočjo hash tabel, ki so še učinkovitejše. V nadaljevanju
 pa predpostavimo, da so naši slovarji [dict] binarna iskalna drevesa, ki v
 vsakem vozlišču hranijo tako ključ kot tudi pripadajočo vrednost, in imajo BST
 strukturo glede na ključe. Ker slovar potrebuje parameter za tip ključa in tip
 vrednosti, ga parametriziramo kot [('key, 'value) dict].
[*-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=*)

type ('a, 'b) dict = ('a * 'b) tree


(*----------------------------------------------------------------------------*]
 Napišite testni primer [test_dict]:
      "b":1
      /    \
  "a":0  "d":2
         /
     "c":-2
[*----------------------------------------------------------------------------*)

let test_dict: (string, int) dict = Node(("b", 1), Node(("a", 0), Empty, Empty), Node(("d", 2), Node(("c", -2), Empty, Empty), Empty))

(*----------------------------------------------------------------------------*]
 Funkcija [dict_get key dict] v slovarju poišče vrednost z ključem [key]. Ker
 slovar vrednosti morda ne vsebuje, vrne [option] tip.
 - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 # dict_get "banana" test_dict;;
 - : 'a option = None
 # dict_get "c" test_dict;;
 - : int option = Some (-2)
[*----------------------------------------------------------------------------*)

let rec dict_get k t =
  match t with
  | Empty -> None
  | Node((k', v), l, r) ->
    if k = k' then Some v
    else if k < k' then dict_get k l
    else dict_get k r

;; assert (dict_get "banana" test_dict = None)
;; assert (dict_get "c" test_dict = Some (-2))
      
(*----------------------------------------------------------------------------*]
 Funkcija [print_dict] sprejme slovar s ključi tipa [string] in vrednostmi tipa
 [int] in v pravilnem vrstnem redu izpiše vrstice "ključ : vrednost" za vsa
 vozlišča slovarja.
 Namig: Uporabite funkciji [print_string] in [print_int]. Nize združujemo z
 operatorjem [^]. V tipu funkcije si oglejte, kako uporaba teh funkcij določi
 parametra za tip ključev in vrednosti v primerjavi s tipom [dict_get].
 - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 # print_dict test_dict;;
 a : 0
 b : 1
 c : -2
 d : 2
 - : unit = ()
[*----------------------------------------------------------------------------*)

let print_dict t =
  let rec a t =
    match t with
    | Empty -> ()
    | Node((k, v), l, r) -> a l; print_string (k ^ " : "); print_int v; print_newline (); a r
  in
  a t

;; print_endline "---"; print_dict test_dict; print_endline "---"

(*----------------------------------------------------------------------------*]
 Funkcija [dict_insert key value dict] v slovar [dict] pod ključ [key] vstavi
 vrednost [value]. Če za nek ključ vrednost že obstaja, jo zamenja.
 - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 # dict_insert "1" 14 test_dict |> print_dict;;
 1 : 14
 a : 0
 b : 1
 c : -2
 d : 2
 - : unit = ()
 # dict_insert "c" 14 test_dict |> print_dict;;
 a : 0
 b : 1
 c : 14
 d : 2
 - : unit = ()
[*----------------------------------------------------------------------------*)

let dict_insert k v d =
  let g = dict_get k d in
  match g with
  | None -> insert (k, v) d
  | Some o -> delete (k, o) d |> insert (k, v)

;; print_endline "---"; dict_insert "1" 14 test_dict |> print_dict; print_endline "---"
;; print_endline "---"; dict_insert "c" 14 test_dict |> print_dict; print_endline "---"

(*----------------------------------------------------------------------------*]
 Napišite primerno signaturo za slovarje [DICT] in naredite implementacijo
 modula z drevesi. 
 
 Modul naj vsebuje prazen slovar [empty] in pa funkcije [get], [insert] in
 [print] (print naj ponovno deluje zgolj na [(string, int) t].
[*----------------------------------------------------------------------------*)

module type DICT = sig
  type ('a, 'b) t
  val empty : ('a, 'b) t
  val get : 'a -> ('a, 'b) t -> 'b option
  val insert : 'a -> 'b -> ('a, 'b) t -> ('a, 'b) t
  val print : (string, int) t -> unit
end

module Tree_dict : DICT = struct
  type ('a, 'b) t = ('a * 'b) tree
  let empty = Empty
  let get = dict_get
  let insert = dict_insert
  let print = print_dict
end

(*----------------------------------------------------------------------------*]
 Funkcija [count (module Dict) list] prešteje in izpiše pojavitve posameznih
 elementov v seznamu [list] s pomočjo izbranega modula slovarjev.
 - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
 # count (module Tree_dict) ["b"; "a"; "n"; "a"; "n"; "a"];;
 a : 3
 b : 1
 n : 2
 - : unit = ()
[*----------------------------------------------------------------------------*)

let count (module Dict: DICT) l =
  let rec a l d =
    match l with
    | [] -> d
    | x :: xs ->
      let g = Dict.get x d in
      match g with
      | None -> a xs (Dict.insert x 1 d)
      | Some o -> a xs (Dict.insert x (o + 1) d)
  in
  let d = Dict.empty in
  let d' = a l d in
  Dict.print d'

;; count (module Tree_dict) ["b"; "a"; "n"; "a"; "n"; "a"]