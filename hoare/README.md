# hoare

There are two ways to formalize assignment in Hoare triple.

One is using substitution,

```coq
Definition substitute (P : assertion) (x : var) (e : exp) : assertion :=
  fun v => P (add v x (eval e v)).

Inductive htriple : assertion -> cmd -> assertion -> Prop :=
| HtAssign : forall P x e, htriple (substitute P x e) (Assign x e) P.
```

Or using existential quantification,

```coq
Inductive htriple : assertion -> cmd -> assertion -> Prop :=
| HtAssign : forall P x e, htriple P (Assign x e) (fun v => exists v', P v' /\ v = add v' x (eval e v)).
```

FRAP uses the second approach with high proof automation, while SF uses the
first one.

One major difference between these two approaches is, the proof flow of the
first one is backward while the second one is forward (also requires some subtle
changes in `HtSeq` and `HtWhile`).

I am attempting the first approach together with proof automation, using CPDT
facility `crush`.

## HOAS

`src/HOAS` is an implementation with high-order abstract syntax, using monadic
`Return` and `Bind` to eliminate valuation map, but less automated. Just for
fun!
