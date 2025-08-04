import Mathlib.Tactic.ApplyAt
import CollapsingTowers.TwoLevelRec.SyntacticTyping.Typing
import CollapsingTowers.TwoLevelRec.SyntacticTyping.Weakening

lemma preservation.maping_strengthened :
  ∀ Δ Φ v e τ𝕒 τ𝕓 τ𝕔 𝕊𝕒 φ,
    typing (Δ ++ (τ𝕔, 𝟙) :: Φ) 𝟙 e τ𝕓 φ →
    typing (Δ ++ (τ𝕒, 𝕊𝕒) :: Φ) 𝟙 v τ𝕔 ∅ →
    typing (Δ ++ (τ𝕒, 𝕊𝕒) :: Φ) 𝟙 (subst Φ.length v e) τ𝕓 φ :=
  by
  intros Δ Φ v e τ𝕒 τ𝕓 τ𝕔 𝕊𝕒 φ
  generalize HEqΓ : Δ ++ (τ𝕔, 𝟙) :: Φ = Γ
  intros Hτe Hτv
  revert Δ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ𝕓 φ (H : typing Γ 𝕊 e τ𝕓 φ) =>
        ∀ Δ,
          Δ ++ (τ𝕔, 𝟙) :: Φ = Γ →
          typing (Δ ++ (τ𝕒, 𝕊𝕒) :: Φ) 𝟙 v τ𝕔 ∅ →
          typing (Δ ++ (τ𝕒, 𝕊𝕒) :: Φ) 𝕊 (subst Φ.length v e) τ𝕓 φ)
      (fun Γ e τ𝕓 φ (H : typing_reification Γ e τ𝕓 φ) =>
        ∀ Δ,
          Δ ++ (τ𝕔, 𝟙) :: Φ = Γ →
          typing (Δ ++ (τ𝕒, 𝕊𝕒) :: Φ) 𝟙 v τ𝕔 ∅ →
          typing_reification (Δ ++ (τ𝕒, 𝕊𝕒) :: Φ) (subst Φ.length v e) τ𝕓 φ)
  <;> intros
  case fvar 𝕊 x _ Hbinds Hwbt Δ HEqΓ Hτv =>
    rw [← HEqΓ] at Hbinds
    cases Hx : compare Φ.length x with
    | lt =>
      rw [compare_lt_iff_lt] at Hx
      simp; rw [if_neg (Nat.ne_of_lt Hx)]
      apply typing.fvar
      have Hx : ((τ𝕒, 𝕊𝕒) :: Φ).length <= x := by simp; omega
      rw [← Nat.add_sub_of_le Hx, Nat.add_comm]
      apply binds.extendr
      apply binds.shrinkr _ ((τ𝕔, 𝟙) :: Φ)
      rw [List.length_cons, List.length_cons, Nat.sub_add_cancel]
      apply Hbinds; omega; apply Hwbt
    | eq =>
      rw [compare_eq_iff_eq] at Hx
      rw [← Hx] at Hbinds
      apply binds.shrink at Hbinds
      simp at Hbinds; rw [← Hbinds.left, ← Hbinds.right]
      simp; rw [if_pos Hx]; apply Hτv; simp
    | gt =>
      rw [compare_gt_iff_gt] at Hx
      simp; rw [if_neg (Nat.ne_of_gt Hx)]
      rw [List.append_cons]
      rw [List.append_cons] at Hbinds
      apply typing.fvar
      apply binds.extend; apply binds.shrink
      omega; apply Hbinds; apply Hwbt
  case lam Hwbt Hclose IH Δ HEqΓ Hτv =>
    rw [← HEqΓ, List.length_append, List.length_cons] at Hclose
    rw [← HEqΓ, comm.subst_opening, List.length_append, List.length_cons] at IH
    apply typing.lam
    rw [← List.cons_append, List.length_append, List.length_cons]
    apply IH; rfl
    apply typing.weakening.singleton; apply Hτv; apply Hwbt
    apply closed.under_subst
    apply typing.closed_at_env; apply Hτv
    rw [List.length_append, List.length_cons]; apply Hclose
    simp; omega
    apply typing.regular; apply Hτv
  case lift_lam IH Δ HEqΓ Hτv =>
    apply typing.lift_lam
    apply IH; apply HEqΓ; apply Hτv
  case lam𝕔 Hwbt Hclose IH Δ HEqΓ Hτv =>
    rw [← HEqΓ, List.length_append, List.length_cons] at Hclose
    rw [← HEqΓ, comm.subst_opening, List.length_append, List.length_cons] at IH
    apply typing.lam𝕔
    rw [← List.cons_append, List.length_append, List.length_cons]
    apply IH; rfl
    apply typing.weakening.singleton; apply Hτv; apply Hwbt
    apply closed.under_subst
    apply typing.closed_at_env; apply Hτv
    rw [List.length_append, List.length_cons]; apply Hclose
    simp; omega; apply typing.regular; apply Hτv
  case app₁ IHf IHarg Δ HEqΓ Hτv =>
    apply typing.app₁
    apply IHf; apply HEqΓ; apply Hτv
    apply IHarg; apply HEqΓ; apply Hτv
  case app₂ IHf IHarg Δ HEqΓ Hτv =>
    apply typing.app₂
    apply IHf; apply HEqΓ; apply Hτv
    apply IHarg; apply HEqΓ; apply Hτv
  case lit => apply typing.lit
  case lift_lit IH Δ HEqΓ Hτv =>
    apply typing.lift_lit
    apply IH; apply HEqΓ; apply Hτv
  case code_fragment x _ Hbinds Hwbt Δ HEqΓ Hτv =>
    rw [← HEqΓ] at Hbinds
    cases Hx : compare Φ.length x with
    | lt =>
      rw [compare_lt_iff_lt] at Hx
      simp; rw [if_neg (Nat.ne_of_lt Hx)]
      apply typing.code_fragment
      have Hx : ((τ𝕒, 𝕊𝕒) :: Φ).length <= x := by simp; omega
      rw [← Nat.add_sub_of_le Hx, Nat.add_comm]
      apply binds.extendr
      apply binds.shrinkr _ ((τ𝕔, 𝟙) :: Φ)
      rw [List.length_cons, List.length_cons, Nat.sub_add_cancel]
      apply Hbinds; omega; apply Hwbt
    | eq =>
      rw [compare_eq_iff_eq] at Hx
      rw [← Hx] at Hbinds
      apply binds.shrink at Hbinds
      simp at Hbinds; simp
    | gt =>
      rw [compare_gt_iff_gt] at Hx
      simp; rw [if_neg (Nat.ne_of_gt Hx)]
      rw [List.append_cons]
      rw [List.append_cons] at Hbinds
      apply typing.code_fragment
      apply binds.extend; apply binds.shrink
      omega; apply Hbinds; apply Hwbt
  case code_rep IH Δ HEqΓ Hτv =>
    apply typing.code_rep
    apply IH; apply HEqΓ; apply Hτv
  case reflect IH Δ HEqΓ Hτv =>
    apply typing.reflect
    apply IH; apply HEqΓ; apply Hτv
  case lets Hwbt Hclose IHb IHe Δ HEqΓ Hτv =>
    rw [← HEqΓ, List.length_append, List.length_cons] at Hclose
    rw [← HEqΓ] at IHb
    rw [← HEqΓ, comm.subst_opening, List.length_append, List.length_cons] at IHe
    apply typing.lets
    apply IHb; rfl; apply Hτv
    rw [← List.cons_append, List.length_append, List.length_cons]
    apply IHe; rfl
    apply typing.weakening.singleton; apply Hτv; apply Hwbt
    apply closed.under_subst
    apply typing.closed_at_env; apply Hτv
    rw [List.length_append, List.length_cons]; apply Hclose
    simp; omega
    apply typing.regular; apply Hτv
  case lets𝕔 Hwbt Hclose IHb IHe Δ HEqΓ Hτv =>
    rw [← HEqΓ, List.length_append, List.length_cons] at Hclose
    rw [← HEqΓ] at IHb
    rw [← HEqΓ, comm.subst_opening, List.length_append, List.length_cons] at IHe
    apply typing.lets𝕔
    apply IHb; rfl; apply Hτv
    rw [← List.cons_append, List.length_append, List.length_cons]
    apply IHe; rfl
    apply typing.weakening.singleton; apply Hτv; apply Hwbt
    apply closed.under_subst
    apply typing.closed_at_env; apply Hτv
    rw [List.length_append, List.length_cons]; apply Hclose
    simp; omega
    apply typing.regular; apply Hτv
  case run Hclose IH Δ HEqΓ Hτv =>
    apply typing.run
    apply IH; apply HEqΓ; apply Hτv
    rw [identity.subst]; apply Hclose
    apply closed.inc; apply Hclose; omega
  case fix₁ Hfixφ _ IH Δ HEqΓ Hτv =>
    apply typing.fix₁; apply Hfixφ
    apply IH; apply HEqΓ; apply Hτv
  case fix₂ IH Δ HEqΓ Hτv =>
    apply typing.fix₂
    apply IH; apply HEqΓ; apply Hτv
  case pure IH Δ HEqΓ Hτv =>
    apply typing_reification.pure
    apply IH; apply HEqΓ; apply Hτv
  case reify IH Δ HEqΓ Hτv =>
    apply typing_reification.reify
    apply IH; apply HEqΓ; apply Hτv
  apply Hτe

theorem preservation.maping :
  ∀ Γ v e τ𝕒 τ𝕓 τ𝕔 𝕊𝕒 φ,
    typing ((τ𝕔, 𝟙) :: Γ) 𝟙 e τ𝕓 φ →
    typing ((τ𝕒, 𝕊𝕒) :: Γ) 𝟙 v τ𝕔 ∅ →
    typing ((τ𝕒, 𝕊𝕒) :: Γ) 𝟙 (subst Γ.length v e) τ𝕓 φ := by
  intros Γ v e τ𝕒 τ𝕓 τ𝕔 𝕊𝕒 φ
  rw [← List.nil_append ((τ𝕔, 𝟙) :: Γ), ← List.nil_append ((τ𝕒, 𝕊𝕒) :: Γ)]
  apply preservation.maping_strengthened
