Section Victor.
Variable (A : Set).

Inductive vic : nat -> Set :=
| vnil : vic 0
| vcons : forall (n : nat), A -> vic n -> vic (S n).


Fixpoint vappend {m n : nat} (v₁ : vic m) (v₂ : vic n) : vic (m + n) :=
  match v₁ with
  | vnil => v₂
  | vcons _ a v₁ => vcons _ a (vappend v₁ v₂)
  end.
End Victor.

Section Map.
  Context {A B : Set}.
  Variable f : A -> B.

  Fixpoint vmap {n : nat} (v : vic A n) : vic B n :=
    match v with
    | vnil _ => vnil _
    | vcons _ _ a v => vcons _ _ (f a) (vmap v)
    end.

  Theorem vmap_vappend : forall {m n : nat} (v₁ : vic A m) (v₂ : vic A n),
      vmap (vappend _ v₁ v₂) = vappend _ (vmap v₁) (vmap v₂).
  Proof.
    intros m n v1; induction v1 as [| p a v1 ih]; intros v2; cbn; f_equal; auto.
  Qed.
End Map.
