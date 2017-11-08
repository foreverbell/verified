Set Implicit Arguments.

Parameter array : Set -> nat -> Set.
Parameter new : forall (A : Set) (n : nat), A -> array A n.
Parameter get : forall (A : Set) (n : nat), array A n -> nat -> A.
Parameter set : forall (A : Set) (n : nat), array A n -> nat -> A -> array A n.

Axiom new_spec :
  forall (A : Set) (n : nat) (v0 : A) (i : nat),
    0 <= i < n -> get (new n v0) i = v0.

Axiom get_spec_1 :
  forall (A : Set) (n : nat) (a : array A n) (v : A) (i : nat),
    0 <= i < n -> get (set a i v) i = v.

Axiom get_spec_2 :
  forall (A : Set) (n : nat) (a : array A n) (v : A) (i j : nat),
    0 <= i < n ->
    0 <= j < n ->
    i <> j ->
    get (set a i v) j = get a j.