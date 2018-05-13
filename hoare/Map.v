Require Import FunctionalExtensionality Classical ClassicalEpsilon.

Set Implicit Arguments.

Module Map.
  Definition map (A B : Type) := A -> B.

  Definition empty A B (def : B) : map A B := fun _ => def.

  Section decidability.
    Variable P : Prop.

    Lemma decided : inhabited (sum P (~P)).
    Proof.
      destruct (classic P).  (** let us cheat a bit here. *)
      constructor; exact (inl _ H).
      constructor; exact (inr _ H).
    Qed.

    Definition decide : sum P (~P) :=
      epsilon decided (fun _ => True).
  End decidability.

  Definition add A B (m : map A B) (k : A) (v : B) : map A B :=
    fun k' => if decide (k' = k) then v else m k'.

  Definition lookup A B (m : map A B) (k : A) : B := m k.

  Global Infix "$" := lookup (at level 30, no associativity).

  Lemma add_eq : forall A B (m : map A B) (k : A) (v : B),
    lookup (add m k v) k = v.
  Proof.
    unfold add, lookup; intros.
    destruct (decide (k = k)); tauto.
  Qed.

  Theorem add_neq : forall A B (m : map A B) (k1 k2 : A) (v : B),
    k1 <> k2 -> lookup (add m k1 v) k2 = lookup m k2.
  Proof.
    unfold add, lookup; intros.
    destruct (decide (k2 = k1)); subst; try tauto.
  Qed.

  Lemma add_shadow : forall A B (m: map A B) (k : A) (v1 v2 : B),
    add (add m k v1) k v2 = add m k v2.
  Proof.
    unfold add; intros; apply functional_extensionality; intros.
    destruct (decide (x = k)); subst; try tauto.
  Qed.

  Theorem add_permute : forall A B (m : map A B) (k1 k2 : A) (v1 v2 : B),
    k1 <> k2 -> (add (add m k2 v2) k1 v1) = (add (add m k1 v1) k2 v2).
  Proof.
    unfold add; intros; apply functional_extensionality; intros.
    destruct (decide (x = k1)); destruct (decide (x = k2)); subst; tauto.
  Qed.
End Map.

Export Map.