import CollapsingTowers.TwoLvLBasic.SyntacticTyping.Typing

lemma typing.shrinking_strengthened :
  ∀ Γ Ψ Δ Φ 𝕊 e τ φ,
    typing Γ 𝕊 e τ φ →
    Γ = Ψ ++ Φ :: Δ →
    Δ.length ∉ fv e →
    typing (Ψ ++ Δ) 𝕊 (shiftr_at Δ.length e) τ φ :=
  by
  intros Γ Ψ Δ Φ 𝕊 e τ φ Hτ
  revert Ψ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ φ (H : typing Γ 𝕊 e τ φ) =>
        ∀ Ψ,
          Γ = Ψ ++ Φ :: Δ →
          Δ.length ∉ fv e →
          typing (Ψ ++ Δ) 𝕊 (shiftr_at Δ.length e) τ φ)
      (fun Γ e τ φ (H : typing_reification Γ e τ φ) =>
        ∀ Ψ,
          Γ = Ψ ++ Φ :: Δ →
          Δ.length ∉ fv e →
          typing_reification (Ψ ++ Δ) (shiftr_at Δ.length e) τ φ)
  <;> intros
  case fvar x _ Hbinds Hwbt Ψ HEqΓ HclosedΔ =>
    rw [HEqΓ] at Hbinds; simp
    cases Hx : compare Δ.length x with
    | lt =>
      rw [compare_lt_iff_lt] at Hx
      rw [if_pos Hx]
      apply typing.fvar
      have Hx : Δ.length <= x - 1 := by omega
      rw [← Nat.add_sub_of_le Hx, Nat.add_comm]
      apply binds.extendr
      rw [← Nat.sub_add_eq, Nat.add_comm]
      apply binds.shrinkr _ (Φ :: Δ)
      rw [List.length_cons, Nat.sub_add_cancel]
      apply Hbinds; omega; apply Hwbt
    | eq =>
      rw [compare_eq_iff_eq] at Hx
      rw [Hx] at HclosedΔ; nomatch HclosedΔ
    | gt =>
      rw [compare_gt_iff_gt] at Hx
      rw [if_neg (Nat.not_lt_of_gt Hx)]
      apply typing.fvar
      apply binds.extend; apply binds.shrink
      omega; rw [List.append_cons] at Hbinds; apply Hbinds; apply Hwbt
  case lam Hwbt Hclosed IH Ψ HEqΓ HclosedΔ =>
    rw [HEqΓ, comm.shiftr_opening] at IH
    rw [HEqΓ] at Hclosed
    apply typing.lam
    simp; rw [← List.cons_append]
    simp at IH; apply IH; rfl
    apply fv.not_in_under_opening; apply HclosedΔ; omega
    apply Hwbt
    simp; apply closed.under_shiftr_dec
    simp at Hclosed; apply Hclosed; apply HclosedΔ
    simp; omega
  case lift_lam IH Ψ HEqΓ HclosedΔ =>
    apply typing.lift_lam
    apply IH; apply HEqΓ; apply HclosedΔ
  case lam𝕔 Hwbt Hclosed IH Ψ HEqΓ HclosedΔ =>
    rw [HEqΓ] at IH; rw [HEqΓ] at Hclosed
    rw [comm.shiftr_opening] at IH
    apply typing.lam𝕔
    simp; rw [← List.cons_append]
    simp at IH; apply IH; rfl
    apply fv.not_in_under_opening; apply HclosedΔ; omega
    apply Hwbt
    simp; apply closed.under_shiftr_dec
    simp at Hclosed; apply Hclosed; apply HclosedΔ
    simp; omega
  case app₁ IHf IHarg Ψ HEqΓ HclosedΔ =>
    simp at HclosedΔ; apply typing.app₁
    apply IHf; apply HEqΓ; apply HclosedΔ.left
    apply IHarg; apply HEqΓ; apply HclosedΔ.right
  case app₂ IHf IHarg Ψ HEqΓ HclosedΔ =>
    simp at HclosedΔ; apply typing.app₂
    apply IHf; apply HEqΓ; apply HclosedΔ.left
    apply IHarg; apply HEqΓ; apply HclosedΔ.right
  case lit => apply typing.lit
  case lift_lit IH Ψ HEqΓ HclosedΔ =>
    apply typing.lift_lit
    apply IH; apply HEqΓ; apply HclosedΔ
  case code_fragment x _ Hbinds Hwbt Ψ HEqΓ HclosedΔ =>
    rw [HEqΓ] at Hbinds; simp
    cases Hx : compare Δ.length x with
    | lt =>
      rw [compare_lt_iff_lt] at Hx
      rw [if_pos Hx]
      apply typing.code_fragment
      have Hx : Δ.length <= x - 1 := by omega
      rw [← Nat.add_sub_of_le Hx, Nat.add_comm]
      apply binds.extendr
      rw [← Nat.sub_add_eq, Nat.add_comm]
      apply binds.shrinkr _ (Φ :: Δ)
      rw [List.length_cons, Nat.sub_add_cancel]
      apply Hbinds; omega; apply Hwbt
    | eq =>
      rw [compare_eq_iff_eq] at Hx
      rw [Hx] at HclosedΔ; nomatch HclosedΔ
    | gt =>
      rw [compare_gt_iff_gt] at Hx
      rw [if_neg (Nat.not_lt_of_gt Hx)]
      apply typing.code_fragment
      apply binds.extend; apply binds.shrink
      omega; rw [List.append_cons] at Hbinds; apply Hbinds; apply Hwbt
  case code_rep IH Ψ HEqΓ HclosedΔ =>
    apply typing.code_rep
    apply IH; apply HEqΓ; apply HclosedΔ
  case reflect IH Ψ HEqΓ HclosedΔ =>
    apply typing.reflect
    apply IH; apply HEqΓ; apply HclosedΔ
  case lets Hwbt Hclosed IHb IHe Ψ HEqΓ HclosedΔ =>
    rw [HEqΓ] at IHb; rw [HEqΓ] at IHe; rw [HEqΓ] at Hclosed
    rw [comm.shiftr_opening] at IHe
    simp at IHb; simp at IHe; simp at HclosedΔ
    apply typing.lets
    apply IHb; apply HclosedΔ.left
    simp; rw [← List.cons_append]; apply IHe; rfl
    apply fv.not_in_under_opening; apply HclosedΔ.right; omega
    apply Hwbt
    simp; apply closed.under_shiftr_dec
    simp at Hclosed; apply Hclosed; apply HclosedΔ.right
    simp; omega
  case lets𝕔 Hwbt Hclosed IHb IHe Ψ HEqΓ HclosedΔ =>
    rw [HEqΓ] at IHb; rw [HEqΓ] at IHe; rw [HEqΓ] at Hclosed
    rw [comm.shiftr_opening] at IHe
    simp at IHb; simp at IHe; simp at HclosedΔ
    apply typing.lets𝕔
    apply IHb; apply HclosedΔ.left
    simp; rw [← List.cons_append]; apply IHe; rfl
    apply fv.not_in_under_opening; apply HclosedΔ.right; omega
    apply Hwbt
    simp; apply closed.under_shiftr_dec
    simp at Hclosed; apply Hclosed; apply HclosedΔ.right
    simp; omega
  case run Hclosed IH Ψ HEqΓ HclosedΔ =>
    apply typing.run
    apply IH; apply HEqΓ; apply HclosedΔ
    rw [identity.shiftr]; apply Hclosed
    apply closed.inc; apply Hclosed; omega
  case pure IH Ψ HEqΓ HclosedΔ =>
    apply typing_reification.pure
    apply IH; apply HEqΓ; apply HclosedΔ
  case reify IH Ψ HEqΓ HclosedΔ =>
    apply typing_reification.reify
    apply IH; apply HEqΓ; apply HclosedΔ
  apply Hτ

theorem typing.shrinking :
  ∀ Γ Φ 𝕊 e τ φ,
    typing (Φ :: Γ) 𝕊 e τ φ →
    closed_at e Γ.length →
    typing Γ 𝕊 e τ φ :=
  by
  intros Γ Φ 𝕊 e τ φ Hτ Hclose
  have H := typing.shrinking_strengthened (Φ :: Γ) [] Γ Φ 𝕊 e τ φ
  rw [identity.shiftr] at H
  apply H; apply Hτ; rfl
  apply closed.impl_fv; apply Hclose; omega
  apply closed.inc; apply Hclose; omega
