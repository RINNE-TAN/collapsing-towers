import Mathlib.Tactic.ApplyAt
import CollapsingTowers.TwoLevelRec.SyntacticTyping.Weakening

lemma preservation.subst_strengthened :
  ∀ Γ Δ Φ v e τ𝕒 τ𝕓 φ,
    typing Γ 𝟙 e τ𝕓 φ →
    Γ = Δ ++ (τ𝕒, 𝟙) :: Φ →
    typing Φ 𝟙 v τ𝕒 ∅ →
    typing (Δ ++ Φ) 𝟙 (shiftr_at Φ.length (subst Φ.length v e)) τ𝕓 φ :=
  by
  intros Γ Δ Φ v e τ𝕒 τ𝕓 φ Hτe HEqΓ
  revert Δ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ𝕓 φ (H : typing Γ 𝕊 e τ𝕓 φ) =>
        ∀ Δ,
          Γ = Δ ++ (τ𝕒, 𝟙) :: Φ →
          typing Φ 𝟙 v τ𝕒 ∅ →
          typing (Δ ++ Φ) 𝕊 (shiftr_at Φ.length (subst Φ.length v e)) τ𝕓 φ)
      (fun Γ e τ𝕓 φ (H : typing_reification Γ e τ𝕓 φ) =>
        ∀ Δ,
          Γ = Δ ++ (τ𝕒, 𝟙) :: Φ →
          typing Φ 𝟙 v τ𝕒 ∅ →
          typing_reification (Δ ++ Φ) (shiftr_at Φ.length (subst Φ.length v e)) τ𝕓 φ)
  <;> intros
  case fvar 𝕊 x _ Hbinds Hwbt Δ HEqΓ Hτv =>
    rw [HEqΓ] at Hbinds; simp
    cases Hx : compare Φ.length x with
    | lt =>
      rw [compare_lt_iff_lt] at Hx
      rw [if_neg (Nat.ne_of_lt Hx)]
      simp; rw [if_pos Hx]
      constructor
      have Hx : Φ.length <= x - 1 := by omega
      rw [← Nat.add_sub_of_le Hx, Nat.add_comm]
      apply binds.extendr
      rw [← Nat.sub_add_eq, Nat.add_comm]
      apply binds.shrinkr _ ((τ𝕒, 𝟙) :: Φ)
      rw [List.length_cons, Nat.sub_add_cancel]
      apply Hbinds; omega; apply Hwbt
    | eq =>
      rw [compare_eq_iff_eq] at Hx
      rw [← Hx] at Hbinds; apply binds.shrink at Hbinds
      simp at Hbinds; rw [← Hbinds.left, ← Hbinds.right]
      rw [if_pos Hx]; rw [identity.shiftr]
      apply typing.weakening; apply Hτv
      apply closed.inc; apply typing.closed_at_env
      apply Hτv; omega; simp
    | gt =>
      rw [compare_gt_iff_gt] at Hx
      rw [if_neg (Nat.ne_of_gt Hx)]
      simp; rw [if_neg (Nat.not_lt_of_gt Hx)]
      constructor
      apply binds.extend; apply binds.shrink
      omega; rw [List.append_cons] at Hbinds; apply Hbinds; apply Hwbt
  case fix Hwbt Hclosed IH Δ HEqΓ Hτv =>
    rw [HEqΓ] at IH Hclosed
    rw [comm.subst_opening, comm.shiftr_opening, comm.subst_opening, comm.shiftr_opening] at IH
    apply typing.fix
    simp; rw [← List.cons_append,← List.cons_append]
    simp at IH; apply IH; rfl
    apply Hτv; apply Hwbt
    simp; apply closed.under_shiftr_dec
    simp at Hclosed
    apply closed.under_subst; apply closed.inc
    apply typing.closed_at_env; apply Hτv; omega; apply Hclosed
    apply fv.not_in_under_subst; apply closed_impl_fv_not_in
    apply typing.closed_at_env; apply Hτv; omega
    simp; omega
    simp; omega
    apply typing.regular; apply Hτv
    simp; omega
    simp; omega
    apply typing.regular; apply Hτv
  case lift_fix IH Δ HEqΓ Hτv =>
    apply typing.lift_fix
    apply IH; apply HEqΓ; apply Hτv
  case fix𝕔 Hwbt Hclosed IH Δ HEqΓ Hτv =>
    rw [HEqΓ] at IH Hclosed
    rw [comm.subst_opening, comm.shiftr_opening, comm.subst_opening, comm.shiftr_opening] at IH
    apply typing.fix𝕔
    simp; rw [← List.cons_append,← List.cons_append]
    simp at IH; apply IH; rfl
    apply Hτv; apply Hwbt
    simp; apply closed.under_shiftr_dec
    simp at Hclosed
    apply closed.under_subst; apply closed.inc
    apply typing.closed_at_env; apply Hτv; omega; apply Hclosed
    apply fv.not_in_under_subst; apply closed_impl_fv_not_in
    apply typing.closed_at_env; apply Hτv; omega
    simp; omega
    simp; omega
    apply typing.regular; apply Hτv
    simp; omega
    simp; omega
    apply typing.regular; apply Hτv
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
    rw [HEqΓ] at Hbinds; simp
    cases Hx : compare Φ.length x with
    | lt =>
      rw [compare_lt_iff_lt] at Hx
      rw [if_neg (Nat.ne_of_lt Hx)]
      simp; rw [if_pos Hx]
      apply typing.code_fragment
      have Hx : Φ.length <= x - 1 := by omega
      rw [← Nat.add_sub_of_le Hx, Nat.add_comm]
      apply binds.extendr
      rw [← Nat.sub_add_eq, Nat.add_comm]
      apply binds.shrinkr _ ((τ𝕒, 𝟙) :: Φ)
      rw [List.length_cons, Nat.sub_add_cancel]
      apply Hbinds; omega; apply Hwbt
    | eq =>
      rw [compare_eq_iff_eq] at Hx
      rw [← Hx] at Hbinds; apply binds.shrink at Hbinds
      simp at Hbinds; simp
    | gt =>
      rw [compare_gt_iff_gt] at Hx
      rw [if_neg (Nat.ne_of_gt Hx)]
      simp; rw [if_neg (Nat.not_lt_of_gt Hx)]
      apply typing.code_fragment
      apply binds.extend; apply binds.shrink
      omega; rw [List.append_cons] at Hbinds; apply Hbinds; apply Hwbt
  case code_rep IH Δ HEqΓ Hτv =>
    apply typing.code_rep
    apply IH; apply HEqΓ; apply Hτv
  case reflect IH Δ HEqΓ Hτv =>
    apply typing.reflect
    apply IH; apply HEqΓ; apply Hτv
  case lets Hwbt Hclosed IHb IHe Δ HEqΓ Hτv =>
    rw [HEqΓ] at IHb IHe Hclosed
    rw [comm.subst_opening, comm.shiftr_opening] at IHe
    simp at IHb; simp at IHe
    apply typing.lets
    apply IHb; apply Hτv
    simp; rw [← List.cons_append]; apply IHe; rfl
    apply Hτv; apply Hwbt
    simp; apply closed.under_shiftr_dec
    simp at Hclosed
    apply closed.under_subst; apply closed.inc
    apply typing.closed_at_env; apply Hτv; omega; apply Hclosed
    apply fv.not_in_under_subst; apply closed_impl_fv_not_in
    apply typing.closed_at_env; apply Hτv; omega
    simp; omega
    simp; omega
    apply typing.regular; apply Hτv
  case lets𝕔 Hwbt Hclosed IHb IHe Δ HEqΓ Hτv =>
    rw [HEqΓ] at IHb IHe Hclosed
    rw [comm.subst_opening, comm.shiftr_opening] at IHe
    simp at IHb; simp at IHe
    apply typing.lets𝕔
    apply IHb; apply Hτv
    simp; rw [← List.cons_append]; apply IHe; rfl
    apply Hτv; apply Hwbt
    simp; apply closed.under_shiftr_dec
    simp at Hclosed
    apply closed.under_subst; apply closed.inc
    apply typing.closed_at_env; apply Hτv; omega; apply Hclosed
    apply fv.not_in_under_subst; apply closed_impl_fv_not_in
    apply typing.closed_at_env; apply Hτv; omega
    simp; omega
    simp; omega
    apply typing.regular; apply Hτv
  case run Hclosed IH Δ HEqΓ Hτv =>
    apply typing.run
    apply IH; apply HEqΓ; apply Hτv
    rw [identity.shiftr, identity.subst]; apply Hclosed
    apply closed.inc; apply Hclosed; omega
    rw [identity.subst]
    apply closed.inc; apply Hclosed; omega
    apply closed.inc; apply Hclosed; omega
  case pure IH Δ HEqΓ Hτv =>
    apply typing_reification.pure
    apply IH; apply HEqΓ; apply Hτv
  case reify IH Δ HEqΓ Hτv =>
    apply typing_reification.reify
    apply IH; apply HEqΓ; apply Hτv
  apply Hτe

theorem preservation.subst :
  ∀ Γ v e τ𝕒 τ𝕓 φ,
    typing Γ 𝟙 v τ𝕒 ∅ →
    typing ((τ𝕒, 𝟙) :: Γ) 𝟙 e τ𝕓 φ →
    typing Γ 𝟙 (subst Γ.length v e) τ𝕓 φ :=
  by
  intros Γ v e τ𝕒 τ𝕓 φ Hτv Hτe
  have H := preservation.subst_strengthened ((τ𝕒, 𝟙) :: Γ) [] Γ v e τ𝕒 τ𝕓 φ
  simp at H
  have H := H Hτe Hτv
  rw [identity.shiftr] at H
  apply H
  apply closed.under_subst
  apply closed.inc; apply typing.closed_at_env; apply Hτv; omega
  rw [← List.length_cons]; apply typing.closed_at_env; apply Hτe
