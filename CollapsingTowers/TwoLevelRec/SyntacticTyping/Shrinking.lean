import CollapsingTowers.TwoLevelRec.SyntacticTyping.Typing

lemma fvar.shrinking :
  ∀ (Ψ Δ : TEnv) Φ 𝕊 x τ,
    Δ.length ≠ x →
    binds x (τ, 𝕊) (Ψ ++ Φ :: Δ) →
    binds (if Δ.length < x then x - 1 else x) (τ, 𝕊) (Ψ ++ Δ) :=
  by
  intros Ψ Δ Φ 𝕊 x τ HNe HBinds
  cases Hx : compare Δ.length x with
  | lt =>
    rw [compare_lt_iff_lt] at Hx
    rw [if_pos Hx]
    have HEq : x - 1 = x - (Φ :: Δ).length + Δ.length := by simp; omega
    rw [HEq]
    apply binds.extendr
    apply binds.shrinkr
    have HEq : x - (Φ :: Δ).length + (Φ :: Δ).length = x := by simp; omega
    rw [HEq]
    apply HBinds
  | eq =>
    rw [compare_eq_iff_eq] at Hx; omega
  | gt =>
    rw [compare_gt_iff_gt] at Hx
    rw [if_neg (Nat.not_lt_of_gt Hx)]
    apply binds.extend
    apply binds.shrink _ (Ψ ++ [Φ]); omega
    simp; apply HBinds

lemma typing.shrinking.strengthened :
  ∀ Γ Ψ Δ Φ 𝕊 e τ φ,
    typing Γ 𝕊 e τ φ →
    Γ = Ψ ++ Φ :: Δ →
    Δ.length ∉ fv e →
    typing (Ψ ++ Δ) 𝕊 (shiftr Δ.length e) τ φ :=
  by
  intros Γ Ψ Δ Φ 𝕊 e τ φ Hτ
  revert Ψ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ φ (H : typing Γ 𝕊 e τ φ) =>
        ∀ Ψ,
          Γ = Ψ ++ Φ :: Δ →
          Δ.length ∉ fv e →
          typing (Ψ ++ Δ) 𝕊 (shiftr Δ.length e) τ φ)
      (fun Γ e τ φ (H : typing_reification Γ e τ φ) =>
        ∀ Ψ,
          Γ = Ψ ++ Φ :: Δ →
          Δ.length ∉ fv e →
          typing_reification (Ψ ++ Δ) (shiftr Δ.length e) τ φ)
  <;> intros
  case fvar x _ HBinds Hwbt Ψ HEqΓ HclosedΔ =>
    rw [HEqΓ] at HBinds
    simp only [shiftr, ← apply_ite]
    apply typing.fvar
    . apply fvar.shrinking
      apply HclosedΔ; apply HBinds
    . apply Hwbt
  case code_fragment x _ HBinds Hwbt Ψ HEqΓ HclosedΔ =>
    rw [HEqΓ] at HBinds
    simp only [shiftr, ← apply_ite]
    apply typing.code_fragment
    . apply fvar.shrinking
      apply HclosedΔ; apply HBinds
    . apply Hwbt
  case lam Hwbt Hclosed IH Ψ HEqΓ HclosedΔ =>
    simp [HEqΓ] at Hclosed
    rw [HEqΓ] at IH
    apply typing.lam
    . have HEq : (Ψ ++ Δ).length = (Ψ ++ Φ :: Δ).length - 1 := by simp
      rw [HEq, ← comm.shiftr_opening]
      apply IH (_ :: Ψ) rfl
      apply not_in_fv.under_opening; apply HclosedΔ
      simp; omega
      simp; omega
    . apply Hwbt
    . simp; apply closed.dec.under_shiftr
      apply Hclosed; apply HclosedΔ
  case lift_lam IH Ψ HEqΓ HclosedΔ =>
    apply typing.lift_lam
    apply IH; apply HEqΓ; apply HclosedΔ
  case lam𝕔 Hwbt Hclosed IH Ψ HEqΓ HclosedΔ =>
    simp [HEqΓ] at Hclosed
    rw [HEqΓ] at IH
    apply typing.lam𝕔
    . have HEq : (Ψ ++ Δ).length = (Ψ ++ Φ :: Δ).length - 1 := by simp
      rw [HEq, ← comm.shiftr_opening]
      apply IH (_ :: Ψ) rfl
      apply not_in_fv.under_opening; apply HclosedΔ
      simp; omega
      simp; omega
    . apply Hwbt
    . simp; apply closed.dec.under_shiftr
      apply Hclosed; apply HclosedΔ
  case app₁ IHf IHarg Ψ HEqΓ HclosedΔ =>
    simp at HclosedΔ; apply typing.app₁
    . apply IHf; apply HEqΓ; apply HclosedΔ.left
    . apply IHarg; apply HEqΓ; apply HclosedΔ.right
  case app₂ IHf IHarg Ψ HEqΓ HclosedΔ =>
    simp at HclosedΔ; apply typing.app₂
    . apply IHf; apply HEqΓ; apply HclosedΔ.left
    . apply IHarg; apply HEqΓ; apply HclosedΔ.right
  case lit => apply typing.lit
  case lift_lit IH Ψ HEqΓ HclosedΔ =>
    apply typing.lift_lit
    apply IH; apply HEqΓ; apply HclosedΔ
  case binary₁ IHl IHr Ψ HEqΓ HclosedΔ =>
    simp at HclosedΔ; apply typing.binary₁
    . apply IHl; apply HEqΓ; apply HclosedΔ.left
    . apply IHr; apply HEqΓ; apply HclosedΔ.right
  case binary₂ IHl IHr Ψ HEqΓ HclosedΔ =>
    simp at HclosedΔ; apply typing.binary₂
    . apply IHl; apply HEqΓ; apply HclosedΔ.left
    . apply IHr; apply HEqΓ; apply HclosedΔ.right
  case code_rep IH Ψ HEqΓ HclosedΔ =>
    apply typing.code_rep
    apply IH; apply HEqΓ; apply HclosedΔ
  case reflect IH Ψ HEqΓ HclosedΔ =>
    apply typing.reflect
    apply IH; apply HEqΓ; apply HclosedΔ
  case lets Hwbt Hclosed IHb IHe Ψ HEqΓ HclosedΔ =>
    simp at HclosedΔ; simp [HEqΓ] at Hclosed
    rw [HEqΓ] at IHe
    apply typing.lets
    . apply IHb; apply HEqΓ; apply HclosedΔ.left
    . have HEq : (Ψ ++ Δ).length = (Ψ ++ Φ :: Δ).length - 1 := by simp
      rw [HEq, ← comm.shiftr_opening]
      apply IHe (_ :: Ψ) rfl
      apply not_in_fv.under_opening; apply HclosedΔ.right
      simp; omega
      simp; omega
    . apply Hwbt
    . simp; apply closed.dec.under_shiftr
      apply Hclosed; apply HclosedΔ.right
  case lets𝕔 Hwbt Hclosed IHb IHe Ψ HEqΓ HclosedΔ =>
    simp at HclosedΔ; simp [HEqΓ] at Hclosed
    rw [HEqΓ] at IHe
    apply typing.lets𝕔
    . apply IHb; apply HEqΓ; apply HclosedΔ.left
    . have HEq : (Ψ ++ Δ).length = (Ψ ++ Φ :: Δ).length - 1 := by simp
      rw [HEq, ← comm.shiftr_opening]
      apply IHe (_ :: Ψ) rfl
      apply not_in_fv.under_opening; apply HclosedΔ.right
      simp; omega
      simp; omega
    . apply Hwbt
    . simp; apply closed.dec.under_shiftr
      apply Hclosed; apply HclosedΔ.right
  case run Hclosed IH Ψ HEqΓ HclosedΔ =>
    apply typing.run
    . apply IH; apply HEqΓ; apply HclosedΔ
    . rw [identity.shiftr]; apply Hclosed
      apply closed.inc; apply Hclosed; omega
  case fix₁ Hfixφ _ IH Ψ HEqΓ HclosedΔ =>
    apply typing.fix₁; apply Hfixφ
    apply IH; apply HEqΓ; apply HclosedΔ
  case fix₂ IH Ψ HEqΓ HclosedΔ =>
    apply typing.fix₂
    apply IH; apply HEqΓ; apply HclosedΔ
  case ifz₁ IHc IHl IHr Ψ HEqΓ HclosedΔ =>
    simp at HclosedΔ; apply typing.ifz₁
    . apply IHc; apply HEqΓ; apply HclosedΔ.left.left
    . apply IHl; apply HEqΓ; apply HclosedΔ.left.right
    . apply IHr; apply HEqΓ; apply HclosedΔ.right
  case ifz₂ IHc IHl IHr Ψ HEqΓ HclosedΔ =>
    simp at HclosedΔ; apply typing.ifz₂
    . apply IHc; apply HEqΓ; apply HclosedΔ.left.left
    . apply IHl; apply HEqΓ; apply HclosedΔ.left.right
    . apply IHr; apply HEqΓ; apply HclosedΔ.right
  case pure IH Ψ HEqΓ HclosedΔ =>
    apply typing_reification.pure
    apply IH; apply HEqΓ; apply HclosedΔ
  case reify IH Ψ HEqΓ HclosedΔ =>
    apply typing_reification.reify
    apply IH; apply HEqΓ; apply HclosedΔ
  apply Hτ

theorem typing.shrinking.singleton :
  ∀ Γ Φ 𝕊 e τ φ,
    typing (Φ :: Γ) 𝕊 e τ φ →
    closed_at e Γ.length →
    typing Γ 𝕊 e τ φ :=
  by
  intros Γ Φ 𝕊 e τ φ Hτ Hclosed
  have H := typing.shrinking.strengthened (Φ :: Γ) ⦰ Γ Φ 𝕊 e τ φ
  rw [identity.shiftr] at H
  apply H; apply Hτ; rfl
  apply closed_impl_not_in_fv; apply Hclosed; omega
  apply closed.inc; apply Hclosed; omega

theorem typing.shrinking :
  ∀ Γ Δ 𝕊 e τ φ,
    typing (Δ ++ Γ) 𝕊 e τ φ →
    closed_at e Γ.length →
    typing Γ 𝕊 e τ φ :=
  by
  intros Γ Δ 𝕊 e τ φ Hτ Hclosed
  induction Δ
  case nil => apply Hτ
  case cons IH =>
    apply IH
    apply typing.shrinking.singleton _ _ _ _ _ _ Hτ
    apply closed.inc; apply Hclosed; simp
