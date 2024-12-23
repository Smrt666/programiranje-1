let endl () = print_endline "";

(*----------------------------------------------------------------------------*
 # Abstrakcija
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 ## Naravna števila
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Definirajte signaturo `NAT`, ki določa strukturo naravnih števil. Ima osnovni
 tip, funkcijo enakosti, ničlo in enko, seštevanje, odštevanje in množenje.
 Hkrati naj vsebuje pretvorbe iz in v OCamlov `int` tip. Opomba: Funkcije za
 pretvarjanje ponavadi poimenujemo `to_int` and `of_int`, tako da skupaj z
 imenom modula dobimo ime `NAT.of_int`, ki nam pove, da pridobivamo naravno
 število iz celega števila.
[*----------------------------------------------------------------------------*)

module type NAT = sig
  type t

  val eq  : t -> t -> bool
  val zero : t
  val one : t
  val to_int : t -> int
  val of_int : int -> t

  val ( ++ ) : t -> t -> t
  val ( -- ) : t -> t -> t
  val ( ** ) : t -> t -> t
end

(*----------------------------------------------------------------------------*
 Napišite implementacijo modula `Nat_int`, ki zgradi modul s signaturo `NAT`,
 kjer kot osnovni tip uporablja OCamlov tip `int`. Namig: dokler ne
 implementirate vse funkcij v `Nat_int`, se bo OCaml pritoževal. Temu se lahko
 izognete tako, da funkcije, ki še niso napisane nadomestite z `failwith
 "later"`, vendar to ne deluje za konstante.
[*----------------------------------------------------------------------------*)

module Nat_int : NAT = struct
  type t = int
  let eq x y = (x = y)
  let zero = 0
  let one = 1
  let to_int (x: t): int = x
  let of_int (x: int): t = x

  let ( ++ ) x y = x + y
  let ( -- ) x y = x - y
  let ( ** ) x y = x * y

end

(*----------------------------------------------------------------------------*
 Napišite implementacijo `NAT`, ki temelji na [Peanovih
 aksiomih](https://en.wikipedia.org/wiki/Peano_axioms). Osnovni tip modula
 definirajte kot naštevni tip, ki vsebuje konstruktor za ničlo in konstruktor za
 naslednika nekega naravnega števila. Večino funkcij lahko implementirate s
 pomočjo rekurzije. Naprimer, enakost števil `k` in `l` določimo s hkratno
 rekurzijo na `k` in `l`, kjer je osnoven primer `Zero = Zero`.
[*----------------------------------------------------------------------------*)

module Nat_peano : NAT = struct

  type t = Zero | Succ of t
  let eq (x: t) (y: t) = (x = y)
  let zero = Zero
  let one = Succ Zero
  let rec to_int x = match x with
  | Zero -> 0
  | Succ x -> 1 + to_int x
  let of_int x = 
    let rec aux x = match x with
    | 0 -> Zero
    | x -> Succ (aux (x-1))
    in if x >= 0 then aux x else failwith "negative number"

  let rec ( ++ ) x y = match x with
  | Zero -> y
  | Succ z -> Succ (z ++ y) 

  let rec ( -- ) x y = match x, y with
  | y, Zero -> x
  | Succ x, Succ y -> x -- y
  | _ -> failwith "negative number"

  let rec ( ** ) x y = match x, y with
  | Zero, _ -> Zero
  | Succ x, y -> y ++ (x ** y)
end;;

(* let test = (
  if Nat_peano.of_int 5 = Nat_peano.of_int 5 then print_endline "true" else print_endline "false";
  if Nat_peano.of_int 4 = Nat_peano.of_int 5 then print_endline "true" else print_endline "false";
) *)

(*----------------------------------------------------------------------------*
 Z ukazom `let module ImeModula = ... in ...` lahko modul definiramo samo
 lokalno. To bomo uporabili za to, da bomo lahko enostavno preklapljali med
 moduloma `Nat_int` in `Nat_peano`, saj bomo enega ali drugega shranili pod ime
 `Nat`. OCaml sicer pozna tudi ustrezne abstrakcije, ki omogočijo preklapljanje
 med moduli, na primer [funktorje](https://ocaml.org/docs/functors) ali
 [prvorazredne module](https://ocaml.org/manual/5.2/firstclassmodules.html), a
 bomo uporabili preprostejšo rešitev.

 Spodnji izračun dopolnite tako, da sešteje prvih 100 naravnih števil. Ker bo
 taka vsota tipa `NAT.t`, ki je abstrakten, končni rezultat pretvorite v tip
 `int` z uporabo funkcije `Nat.to_int`. Če ste oba modula implementirali
 pravilno, bi morali dobiti enak rezultat ne glede na to, katerega poimenujete
 `Nat`.
[*----------------------------------------------------------------------------*)

let sum_nat_100, prod, diff = 
  (* let module Nat = Nat_int in *)
  let module Nat = Nat_peano in
  let ( ++ ) = Nat.( ++ ) in
  let ( ** ) = Nat.( ** ) in
  let ( -- ) = Nat.( -- ) in
  let rec sum n acc = if n = 0 then acc else sum (n-1) (acc ++ (Nat.of_int n)) in
  sum 100 Nat.zero |> Nat.to_int, 
  ((Nat.one ++ Nat.one) ** (Nat.one ++ Nat.one ++ Nat.one)) |> Nat.to_int,
  ((Nat.of_int 5) -- (Nat.of_int 3)) |> Nat.to_int;;
;;

print_int sum_nat_100; endl ();
print_int prod; endl ();
print_int diff; endl ();;


(*----------------------------------------------------------------------------*
 ## Kompleksna števila
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 > Once upon a time, there was a university with a peculiar tenure
 > policy. All faculty were tenured, and could only be dismissed for
 > moral turpitude. What was peculiar was the definition of moral
 > turpitude: making a false statement in class. Needless to say, the
 > university did not teach computer science. However, it had a renowned
 > department of mathematics.
 >
 > One Semester, there was such a large enrollment in complex variables
 > that two sections were scheduled. In one section, Professor Descartes
 > announced that a complex number was an ordered pair of reals, and that
 > two complex numbers were equal when their corresponding components
 > were equal. He went on to explain how to convert reals into complex
 > numbers, what "i" was, how to add, multiply, and conjugate complex
 > numbers, and how to find their magnitude.
 >
 > In the other section, Professor Bessel announced that a complex number
 > was an ordered pair of reals the first of which was nonnegative, and
 > that two complex numbers were equal if their first components were
 > equal and either the first components were zero or the second
 > components differed by a multiple of 2π. He then told an entirely
 > different story about converting reals, "i", addition, multiplication,
 > conjugation, and magnitude.
 >
 > Then, after their first classes, an unfortunate mistake in the
 > registrar's office caused the two sections to be interchanged. Despite
 > this, neither Descartes nor Bessel ever committed moral turpitude,
 > even though each was judged by the other's definitions. The reason was
 > that they both had an intuitive understanding of type. Having defined
 > complex numbers and the primitive operations upon them, thereafter
 > they spoke at a level of abstraction that encompassed both of their
 > definitions.
 >
 > The moral of this fable is that: Type structure is a syntactic
 > discipline for enforcing levels of abstraction.
 >
 > John C. Reynolds, _Types, Abstraction, and Parametric Polymorphism_, IFIP83
[*----------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------*
 Definirajte signaturo modula kompleksnih števil. Potrebujemo osnovni tip, test
 enakosti, ničlo, enko, imaginarno konstanto i, negacijo, konjugacijo,
 seštevanje in množenje.
[*----------------------------------------------------------------------------*)

module type COMPLEX = sig
  type t
  val eq : t -> t -> bool
  val zero : t
  val one : t
  val i : t
  val neg : t -> t
  val conj : t -> t
  val ( ++ ) : t -> t -> t
  val ( ** ) : t -> t -> t

  val to_string : t -> string
end

(*----------------------------------------------------------------------------*
 Napišite kartezično implementacijo kompleksnih števil, kjer ima vsako
 kompleksno število realno in imaginarno komponento.
[*----------------------------------------------------------------------------*)

module Cartesian : COMPLEX = struct

  type t = {re : float; im : float}

  let eq x y = failwith "later"
  let zero = {re = 0.; im = 0.}
  let one = {re = 1.; im = 0.}
  let i = {re = 0.; im = 1.}
  let neg x = {re = -.x.re; im = -.x.im}
  let conj x = {x with im = -.x.im}
  let ( ++ ) x y = {re = x.re +. y.re; im = x.im +. y.im}
  let ( ** ) x y = {re = x.re *. y.re -. x.im *. y.im; im = x.re *. y.im +. x.im *. y.re}

  let to_string x = Printf.sprintf "%.2f + %.2fi" x.re x.im

end

(*----------------------------------------------------------------------------*
 Sedaj napišite še polarno implementacijo kompleksnih števil, kjer ima vsako
 kompleksno število radij in kot (angl. magnitude in argument). Priporočilo:
 Seštevanje je v polarnih koordinatah zahtevnejše, zato si ga pustite za konec
 (lahko tudi za konec stoletja).
[*----------------------------------------------------------------------------*)

module Polar : COMPLEX = struct

  type t = {magn : float; arg : float}

  (* Pomožne funkcije za lažje življenje. *)
  let pi = 2. *. acos 0.
  let rad_of_deg deg = (deg /. 180.) *. pi
  let deg_of_rad rad = (rad /. pi) *. 180.

  let eq x y = if x.magn = 0. && x.magn = y.magn then true else ((x.magn = y.magn) && (mod_float (x.arg -. y.arg) (2. *. pi) = 0.))
  let zero = {magn = 0.; arg = 0.}
  let one = {magn = 1.; arg = 0.}
  let i = {magn = 1.; arg = pi /. 2.}
  let neg x = {x with arg = mod_float (x.arg +. pi) (2. *. pi)}

  let conj x = {x with arg = mod_float (-.x.arg) (2. *. pi)}

  let ( ++ ) x y = 
    let x_re = x.magn *. cos x.arg in
    let x_im = x.magn *. sin x.arg in
    let y_re = y.magn *. cos y.arg in
    let y_im = y.magn *. sin y.arg in
    let re = x_re +. y_re in
    let im = x_im +. y_im in
    {magn = sqrt (re *. re +. im *. im); arg = atan2 im re}
  let ( ** ) x y = {magn = x.magn *. y.magn; arg = mod_float (x.arg +. y.arg) (2. *. pi)}

  let to_string x = Printf.sprintf "%.2f + %.2fi" (x.magn *. cos x.arg) (x.magn *. sin x.arg)

end;;

let module Complex = Polar in
  let ( ++ ) = Complex.( ++ ) in
  let ( ** ) = Complex.( ** ) in
  let two = Complex.one ++ Complex.one in
  let four = two ** two in
  let i = Complex.i in
  let a = two ++ i ** four in
  let b = Complex.one ++ i in
  let s = a ++ b in
  print_string (Complex.to_string s); endl ();;