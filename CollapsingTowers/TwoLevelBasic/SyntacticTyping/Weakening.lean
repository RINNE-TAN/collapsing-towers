import CollapsingTowers.TwoLevelBasic.SyntacticTyping.Typing

lemma fvar.weakening :
  ∀ (Ψ Δ Φ : TEnv) 𝕊 x τ,
    binds x (τ, 𝕊) (Ψ ++ Φ) →
    binds (if Φ.length ≤ x then x + Δ.length else x) (τ, 𝕊) (Ψ ++ Δ ++ Φ) :=
  by
  intros Ψ Δ Φ 𝕊 x τ HBinds
  by_cases HLe : Φ.length <= x
  . rw [if_pos HLe]
    have HEq : x + Δ.length = x - Φ.length + Δ.length + Φ.length := by omega
    rw [HEq]
    apply binds.extendr
    apply binds.extendr
    apply binds.shrinkr
    have HEq : x - Φ.length + Φ.length = x := by omega
    rw [HEq]
    apply HBinds
  . rw [if_neg HLe]
    apply binds.extend
    apply binds.shrink; omega
    apply HBinds

theorem typing.weakening.strengthened :
    ∀ Γ Ψ Δ Φ 𝕊 e τ φ,
      typing Γ 𝕊 e τ φ →
      Γ = Ψ ++ Φ →
      typing (Ψ ++ Δ ++ Φ) 𝕊 (shiftl Φ.length Δ.length e) τ φ :=
  by
  intros Γ Ψ Δ Φ 𝕊 e τ φ Hτ HEqΓ
  revert Ψ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ φ (H : typing Γ 𝕊 e τ φ) =>
        ∀ Ψ,
          Γ = Ψ ++ Φ →
          typing (Ψ ++ Δ ++ Φ) 𝕊 (shiftl Φ.length Δ.length e) τ φ)
      (fun Γ e τ φ (H : typing_reification Γ e τ φ) =>
        ∀ Ψ,
          Γ = Ψ ++ Φ →
          typing_reification (Ψ ++ Δ ++ Φ) (shiftl Φ.length Δ.length e) τ φ)
  <;> intros
  case fvar HBinds Hwbt Ψ HEqΓ =>
    rw [HEqΓ] at HBinds
    simp only [shiftl, ← apply_ite]
    apply typing.fvar
    . apply fvar.weakening
      apply HBinds
    . apply Hwbt
  case code_fragment HBinds Hwbt Ψ HEqΓ =>
    rw [HEqΓ] at HBinds
    simp only [shiftl, ← apply_ite]
    apply typing.code_fragment
    . apply fvar.weakening
      apply HBinds
    . apply Hwbt
  case lam Hwbt Hclosed IH Ψ HEqΓ =>
    rw [HEqΓ] at Hclosed IH
    have HEq : (Ψ ++ Δ ++ Φ).length = (Ψ ++ Φ).length + Δ.length := by simp; omega
    apply typing.lam
    . rw [HEq, ← comm.shiftl_opening]
      apply IH (_ :: Ψ) rfl
      simp
    . apply Hwbt
    . rw [HEq]
      apply closed.under_shiftl _ _ _ _ Hclosed
  case lam𝕔 Hwbt Hclosed IH Ψ HEqΓ =>
    rw [HEqΓ] at Hclosed IH
    have HEq : (Ψ ++ Δ ++ Φ).length = (Ψ ++ Φ).length + Δ.length := by simp; omega
    apply typing.lam𝕔
    . rw [HEq, ← comm.shiftl_opening]
      apply IH (_ :: Ψ) rfl
      simp
    . apply Hwbt
    . rw [HEq]
      apply closed.under_shiftl _ _ _ _ Hclosed
  case lift_lam IH Ψ HEqΓ =>
    apply typing.lift_lam
    apply IH; apply HEqΓ
  case app₁ IHf IHarg Ψ HEqΓ =>
    apply typing.app₁
    . apply IHf; apply HEqΓ
    . apply IHarg; apply HEqΓ
  case app₂ IHf IHarg Ψ HEqΓ =>
    apply typing.app₂
    . apply IHf; apply HEqΓ
    . apply IHarg; apply HEqΓ
  case lit => apply typing.lit
  case lift_lit IH Ψ HEqΓ =>
    apply typing.lift_lit
    apply IH; apply HEqΓ
  case code_rep IH Ψ HEqΓ =>
    apply typing.code_rep
    apply IH; apply HEqΓ
  case reflect IH Ψ HEqΓ =>
    apply typing.reflect
    apply IH; apply HEqΓ
  case lets Hwbt Hclosed IHb IHe Ψ HEqΓ =>
    rw [HEqΓ] at Hclosed IHe
    have HEq : (Ψ ++ Δ ++ Φ).length = (Ψ ++ Φ).length + Δ.length := by simp; omega
    apply typing.lets
    . apply IHb; apply HEqΓ
    . rw [HEq, ← comm.shiftl_opening]
      apply IHe (_ :: Ψ) rfl
      simp
    . apply Hwbt
    . rw [HEq]
      apply closed.under_shiftl _ _ _ _ Hclosed
  case lets𝕔 Hwbt Hclosed IHb IHe Ψ HEqΓ =>
    rw [HEqΓ] at Hclosed IHe
    have HEq : (Ψ ++ Δ ++ Φ).length = (Ψ ++ Φ).length + Δ.length := by simp; omega
    apply typing.lets𝕔
    . apply IHb; apply HEqΓ
    . rw [HEq, ← comm.shiftl_opening]
      apply IHe (_ :: Ψ) rfl
      simp
    . apply Hwbt
    . rw [HEq]
      apply closed.under_shiftl _ _ _ _ Hclosed
  case run Hclosed IH Ψ HEqΓ =>
    apply typing.run
    . apply IH; apply HEqΓ
    . rw [identity.shiftl]; apply Hclosed
      apply closed.inc; apply Hclosed; omega
  case pure IH Ψ HEqΓ =>
    apply typing_reification.pure
    apply IH; apply HEqΓ
  case reify IH Ψ HEqΓ =>
    apply typing_reification.reify
    apply IH; apply HEqΓ
  apply Hτ

theorem typing.weakening :
  ∀ Γ Δ 𝕊 e τ φ,
    typing Γ 𝕊 e τ φ →
    typing (Δ ++ Γ) 𝕊 e τ φ :=
  by
  intros Γ Δ 𝕊 e τ φ Hτ
  rw [← List.nil_append Δ]
  rw [← identity.shiftl _ e]
  apply typing.weakening.strengthened
  apply Hτ; rfl
  apply typing.closed_at_env; apply Hτ

theorem typing.weakening.singleton :
  ∀ Γ Δ 𝕊 e τ φ,
    typing Γ 𝕊 e τ φ →
    typing (Δ :: Γ) 𝕊 e τ φ :=
  by
  intros Γ Δ 𝕊 e τ φ
  rw [← List.singleton_append]
  apply typing.weakening

theorem typing_reification.weakening :
  ∀ Γ Δ e τ φ,
    typing_reification Γ e τ φ →
    typing_reification (Δ ++ Γ) e τ φ :=
  by
  intros Γ Δ e τ φ Hτ
  cases Hτ
  case pure Hτ =>
    apply typing_reification.pure
    apply typing.weakening _ _ _ _ _ _ Hτ
  case reify Hτ =>
    apply typing_reification.reify
    apply typing.weakening _ _ _ _ _ _ Hτ
