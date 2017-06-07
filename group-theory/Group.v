Require Import Setoid.

(* Derived from https://people.cs.umass.edu/~arjun/courses/cs691pl-spring2014/assignments/groups.html,
   but without any automation. *)

Section Group.

(* The set of the group. *)
Variable G : Set.

(* The binary operator. *)
Variable f : G -> G -> G.
Infix "*" := f (at level 40, left associativity).

(* The group identity. *)
Variable e : G.

(* The inverse operator. *)
Variable i : G -> G.

(* The operator [f] is associative. *)
Variable assoc : forall (a b c : G), (a * b) * c = a * (b * c).

(* [e] is the left-identity for all elements [a]. *)
Variable id_l : forall (a : G), e * a = a.

(* [i a] is the left-inverse of [a]. *)
Variable inv_l : forall (a : G), i a * a = e.

(* Theorems in group theory. *)

(* The identity [e] is unique. *)
Theorem e_unique :
  forall (a : G), a * a = a -> a = e.
Proof.
  intros.
  rewrite <- (id_l a) at 1.
  rewrite <- (inv_l a).
  rewrite assoc.
  rewrite H. auto.
Qed.

(* [i a] is the right-inverse of [a]. *)
Theorem inv_r :
  forall (a : G), a * i a = e.
Proof.
  intros.
  apply e_unique.
  rewrite assoc. rewrite <- (assoc (i a) a (i a)).
  rewrite inv_l.
  rewrite id_l. auto.
Qed.

(* [e] is the right-identity. *)
Theorem id_r :
  forall (a : G), a * e = a.
Proof.
  intros.
  rewrite <- (inv_l a).
  rewrite <- assoc.
  rewrite inv_r, id_l.
  auto.
Qed.

(* [x] can be cancelled on the left. *)
Theorem cancel_l :
  forall (a b x : G), x * a = x * b -> a = b.
Proof.
  intros.
  rewrite <- (id_l a), <- (id_l b).
  rewrite <- (inv_l x).
  rewrite assoc, assoc.
  rewrite H.
  auto.
Qed.

(* [x] can be cancelled on the right. *)
Theorem cancel_r :
  forall (a b x : G), a * x = b * x -> a = b.
Proof.
  intros.
  rewrite <- (id_r a), <- (id_r b).
  rewrite <- (inv_r x).
  rewrite <- assoc, <- assoc.
  rewrite H.
  auto.
Qed.

(* The left identity is unique. *)
Theorem e_uniq_l :
  forall (a x : G), x * a = a -> x = e.
Proof.
  intros.
  apply (cancel_r _ _ a).
  rewrite id_l.
  auto.
Qed.

(* The left inverse is unique. *)
Theorem inv_uniq_l :
  forall (a b : G), a * b = e -> a = i b.
Proof.
  intros.
  apply (cancel_r _ _ (b * e)).
  rewrite <- assoc, <- assoc.
  rewrite H, id_l, inv_l.
  rewrite id_l.
  auto.
Qed.

(* The left identity is unique. *)
Theorem e_uniq_r :
  forall (a x : G), a * x = a -> x = e.
Proof.
  intros.
  apply (cancel_l _ _ a).
  rewrite id_r.
  auto.
Qed.

(* The right inverse is unique. *)
Theorem inv_uniq_r :
  forall (a b : G), a * b = e -> b = i a.
Proof.
  intros.
  apply (cancel_l _ _ (e * a)).
  rewrite assoc, assoc.
  rewrite H, id_r, inv_r.
  rewrite id_r.
  auto.
Qed.

(* The inverse operator distributes over the group operator. *)
Theorem inv_distr :
  forall (a b : G), i (a * b) = i b * i a.
Proof.
  intros. symmetry.
  apply inv_uniq_l.
  rewrite assoc. rewrite <- (assoc (i a) a b).
  rewrite inv_l.
  rewrite id_l.
  rewrite inv_l.
  auto.
Qed.

(* The inverse of an inverse produces the original element. *)
Theorem double_inv : forall (a : G), i (i a) = a.
Proof.
  intros. symmetry.
  apply inv_uniq_l.
  apply inv_r.
Qed.

(* The identity is its own inverse. *)
Theorem id_inv : i e = e.
Proof.
  intros. symmetry.
  apply inv_uniq_l.
  apply id_l.
Qed.

Theorem inv_a_eq_a_implies_abelian :
  (forall (a : G), a = i a) -> forall (x y : G), x * y = y * x.
Proof.
  intros.
  assert (x = i x) as H1.
  { apply H. }
  assert (y = i y) as H2.
  { apply H. }
  assert ((y * x) = i (y * x)) as H3.
  { apply H. }
  rewrite inv_distr in H3.
  rewrite H1 at 1.
  rewrite H2 at 1.
  auto.
Qed.

End Group.
