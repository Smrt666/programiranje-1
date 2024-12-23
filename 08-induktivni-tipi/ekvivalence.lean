def concat {A : Type} : List A → List A → List A :=
  fun xs ys =>
    match xs with
    | [] => ys
    | x :: xs' => x :: concat xs' ys

#eval (concat ["a", "b"] ["c", "d"])

def reverse {A : Type} : List A → List A :=
  fun xs =>
    match xs with
    | [] => []
    | x :: xs' => concat (reverse xs') [x]


#eval (reverse ["a", "b", "c", "d"])

def length {A : Type} : List A → Nat :=
  fun xs =>
    match xs with
    | [] => 0
    | _ :: xs' => 1 + length xs'


#eval (length ["a", "b", "c", "d"])

theorem trd1  {A : Type} {x : A} : reverse [x] = [x] :=
  by
    simp [reverse, concat]

theorem trd2 {A : Type} {xs ys : List A} : length (concat xs ys) = length xs + length ys :=
  by
    induction xs with
    | nil =>
      simp [concat, length]
    | cons x xs' ih =>
      simp [concat, length]
      rw [ih]
      simp [Nat.add_assoc]

-- Tega poznamo že iz predavanj
theorem trd3 {A : Type} {xs : List A} : concat xs [] = xs :=
  by
    induction xs with
    | nil =>
      simp [concat]
    | cons x xs' ih =>
      simp [concat]
      rw [ih]

theorem trd4 {A : Type} {xs ys zs : List A} : concat (concat xs ys) zs = concat xs (concat ys zs) :=
  by
    induction xs with
    | nil =>
      simp [concat]
    | cons x xs' ih =>
      simp [concat]
      rw [ih]

theorem trd5 {A : Type} {xs ys : List A} : reverse (concat xs ys) = concat (reverse ys) (reverse xs) :=
  by
    induction xs with
    | nil =>
      simp [concat, reverse, trd3]
    | cons x xs' ih =>
      simp [concat, reverse]
      rw [ih]
      simp [trd4]

theorem trd6 {A : Type} {xs : List A} : length (reverse xs) = length xs :=
  by
    induction xs with
    | nil => simp [reverse, length]
    | cons x xs' ih =>
      simp [reverse, trd2, length]
      rw [ih]
      rw [Nat.add_comm]

theorem trd7 {A : Type} {xs : List A} : reverse (reverse xs) = xs :=
  by
    induction xs with
    | nil => simp [reverse]
    | cons x xs' ih =>
      simp [reverse]
      rw [trd5]
      rw [ih]
      simp [trd1, concat]

def map {A B : Type} : (A → B) → List A → List B :=
  fun f xs =>
    match xs with
    | [] => []
    | x :: xs' => (f x) :: map f xs'

theorem map_assoc {A B C : Type} {f : A → B} {g : B → C} {xs : List A} : map g (map f xs) = map (g ∘ f) xs :=
  by
    induction xs with
    | nil => simp [map]
    | cons x xs' ih =>
      simp [map]
      rw [ih]

theorem map_id {A : Type} {xs : List A} : map id xs = xs :=
  by
    induction xs with
    | nil => simp [map]
    | cons x xs' ih =>
      simp [map]
      exact ih

theorem map_concat {A B : Type} {f : A → B} {xs ys : List A} : map f (concat xs ys) = concat (map f xs) (map f ys) :=
  by
    induction xs with
    | nil => simp [map, concat]
    | cons x xs' ih =>
      simp [concat, map]
      rw [ih]

theorem map_reverse {A B : Type} {f : A → B} {xs : List A} : map f (reverse xs) = reverse (map f xs) :=
  by
    induction xs with
    | nil => simp [reverse, map]
    | cons x xs' ih =>
      simp [reverse]
      rw [← ih]
      simp [map_concat, map]

inductive tree (A : Type) : Type where
  | empty : tree A
  | node : A → tree A → tree A → tree A

#check tree.rec

def tree_map {A B : Type} : (A → B) → tree A → tree B :=
  fun f ta =>
    match ta with
    | tree.empty => tree.empty
    | tree.node a tl tr => tree.node (f a) (tree_map f tl) (tree_map f tr)

theorem tree_map_empty {A B : Type} {f : A → B} : tree_map f tree.empty = tree.empty :=
  by
    simp [tree_map]

theorem tree_map_comp {A B C : Type} {f : A → B} {g : B → C} {t : tree A} : tree_map g (tree_map f t) = tree_map (g ∘ f) t :=
  by
    induction t with
    | empty =>
      simp [tree_map]
    | node n tl tr ihl ihr =>
      simp [tree_map]
      rw [ihl, ihr]
      constructor
      rfl
      rfl

def depth {A : Type} : tree A → Nat :=
  fun t =>
    match t with
    | tree.empty => 0
    | tree.node _ l r => 1 + Nat.max (depth l) (depth r)

-- S tem se ne bomo ukvarjali
theorem max_comm {a b : Nat} : Nat.max a b = Nat.max b a :=
  sorry

def mirror {A : Type} : tree A → tree A :=
  fun t =>
    match t with
    | tree.empty => tree.empty
    | tree.node n l r => tree.node n (mirror l) (mirror r)

theorem mirror_depth {A : Type} {t : tree A} : depth (mirror t) = depth t :=
  by
    induction t with
    | empty => simp [mirror]
    | node n l r ihl ihr =>
      simp [mirror, depth]
      rw [ihl, ihr]

theorem mirror_mirror {A : Type} {t : tree A} : mirror (mirror t) = t :=
  by
    induction t with
    | empty => simp [mirror]
    | node n l r ihl ihr =>
      simp [mirror]
      constructor
      exact ihl
      exact ihr

def collect {A : Type} : tree A → List A :=
  fun t =>
    match t with
    | tree.empty => []
    | tree.node x l r => concat (collect l) (concat [x]  (collect r))

theorem trd8 {A : Type} {x : A} {xs ys : List A} : concat xs (x::ys) = concat (concat xs [x]) ys :=
  by
    simp [trd4, concat]

theorem collect_mirror {A : Type} {t : tree A} : collect (mirror t) = reverse (collect t) :=
  by
    induction t with
    | empty => simp [mirror, collect, reverse]
    | node n l r ihl ihr =>
      simp [mirror, collect, concat]
      rw [ihl, ihr]
      sorry



def size {A : Type} : tree A → Nat :=
  sorry

theorem size_mirror {A : Type} {t : tree A} : size (mirror t) = size t :=
  sorry
