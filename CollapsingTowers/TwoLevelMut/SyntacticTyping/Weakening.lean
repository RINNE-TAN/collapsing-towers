import CollapsingTowers.TwoLevelMut.SyntacticTyping.Typing

lemma fvar.weakening :
  ∀ (Ψ Δ Φ : TEnv) 𝕊 x τ,
    binds x (τ, 𝕊) (Ψ ++ Φ) →
    binds (if Φ.length ≤ x then x + Δ.length else x) (τ, 𝕊) (Ψ ++ Δ ++ Φ) :=
  by
  intros Ψ Δ Φ 𝕊 x τ Hbinds
  by_cases HLe : Φ.length <= x
  . rw [if_pos HLe]
    have HEq : x + Δ.length = x - Φ.length + Δ.length + Φ.length := by omega
    rw [HEq]
    apply binds.extendr
    apply binds.extendr
    apply binds.shrinkr
    have HEq : x - Φ.length + Φ.length = x := by omega
    rw [HEq]
    apply Hbinds
  . rw [if_neg HLe]
    apply binds.extend
    apply binds.shrink; omega
    apply Hbinds

theorem typing.weakening.strengthened :
    ∀ σ Γ Ψ Δ Φ 𝕊 e τ φ,
      typing σ Γ 𝕊 e τ φ →
      Γ = Ψ ++ Φ →
      typing σ (Ψ ++ Δ ++ Φ) 𝕊 (shiftl Φ.length Δ.length e) τ φ :=
  by
  intros σ Γ Ψ Δ Φ 𝕊 e τ φ Hτ HEqΓ
  revert Ψ
  apply
    @typing.rec σ
      (fun Γ 𝕊 e τ φ (H : typing σ Γ 𝕊 e τ φ) =>
        ∀ Ψ,
          Γ = Ψ ++ Φ →
          typing σ (Ψ ++ Δ ++ Φ) 𝕊 (shiftl Φ.length Δ.length e) τ φ)
      (fun Γ e τ φ (H : typing_reification σ Γ e τ φ) =>
        ∀ Ψ,
          Γ = Ψ ++ Φ →
          typing_reification σ (Ψ ++ Δ ++ Φ) (shiftl Φ.length Δ.length e) τ φ)
  <;> intros
  case fvar Hbinds Hwbt Ψ HEqΓ =>
    rw [HEqΓ] at Hbinds
    simp only [shiftl, ← apply_ite]
    apply typing.fvar
    . apply fvar.weakening
      apply Hbinds
    . apply Hwbt
  case code_fragment Hbinds Hwbt Ψ HEqΓ =>
    rw [HEqΓ] at Hbinds
    simp only [shiftl, ← apply_ite]
    apply typing.code_fragment
    . apply fvar.weakening
      apply Hbinds
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
  case unit => apply typing.unit
  case loc Hloc Ψ HEqΓ =>
    apply typing.loc; apply Hloc
  case load₁ IH Ψ HEqΓ =>
    apply typing.load₁
    apply IH; apply HEqΓ
  case load₂ IH Ψ HEqΓ =>
    apply typing.load₂
    apply IH; apply HEqΓ
  case alloc₁ IH Ψ HEqΓ =>
    apply typing.alloc₁
    apply IH; apply HEqΓ
  case alloc₂ IH Ψ HEqΓ =>
    apply typing.alloc₂
    apply IH; apply HEqΓ
  case store₁ IH₀ IH₁ Ψ HEqΓ =>
    apply typing.store₁
    . apply IH₀; apply HEqΓ
    . apply IH₁; apply HEqΓ
  case store₂ IH₀ IH₁ Ψ HEqΓ =>
    apply typing.store₂
    . apply IH₀; apply HEqΓ
    . apply IH₁; apply HEqΓ
  case pure IH Ψ HEqΓ =>
    apply typing_reification.pure
    apply IH; apply HEqΓ
  case reify IH Ψ HEqΓ =>
    apply typing_reification.reify
    apply IH; apply HEqΓ
  apply Hτ

theorem typing.weakening :
  ∀ σ Γ Δ 𝕊 e τ φ,
    typing σ Γ 𝕊 e τ φ →
    typing σ (Δ ++ Γ) 𝕊 e τ φ :=
  by
  intros σ Γ Δ 𝕊 e τ φ Hτ
  rw [← List.nil_append Δ]
  rw [← identity.shiftl _ e]
  apply typing.weakening.strengthened
  apply Hτ; rfl
  apply typing.closed_at_env; apply Hτ

theorem typing.weakening.singleton :
  ∀ σ Γ Δ 𝕊 e τ φ,
    typing σ Γ 𝕊 e τ φ ->
    typing σ (Δ :: Γ) 𝕊 e τ φ :=
  by
  intros σ Γ Δ 𝕊 e τ
  rw [← List.singleton_append]
  apply typing.weakening

theorem typing_reification.weakening : ∀ σ Γ Δ e τ φ, typing_reification σ Γ e τ φ → typing_reification σ (Δ ++ Γ) e τ φ :=
  by
  intros σ Γ Δ e τ φ Hτ
  cases Hτ
  case pure Hτ =>
    apply typing_reification.pure
    apply typing.weakening _ _ _ _ _ _ _ Hτ
  case reify Hτ =>
    apply typing_reification.reify
    apply typing.weakening _ _ _ _ _ _ _ Hτ

theorem typing.weakening.store :
  ∀ σ₀ σ₁ Γ 𝕊 e τ φ,
    σ₀.length ≤ σ₁.length →
    typing σ₀ Γ 𝕊 e τ φ →
    typing σ₁ Γ 𝕊 e τ φ :=
  by
  intros σ₀ σ₁ Γ 𝕊 e τ φ Hσ Hτ
  apply
    @typing.rec σ₀
      (fun Γ 𝕊 e τ φ (H : typing σ₀ Γ 𝕊 e τ φ) => typing σ₁ Γ 𝕊 e τ φ)
      (fun Γ e τ φ (H : typing_reification σ₀ Γ e τ φ) => typing_reification σ₁ Γ e τ φ)
  <;> intros
  case fvar Hbinds Hwbt =>
    apply typing.fvar
    apply Hbinds; apply Hwbt
  case lam Hwbt Hclosed IH =>
    apply typing.lam
    . apply IH
    . apply Hwbt
    . apply Hclosed
  case lift_lam IH =>
    apply typing.lift_lam
    apply IH
  case app₁ IHf IHarg =>
    apply typing.app₁
    . apply IHf
    . apply IHarg
  case app₂ IHf IHarg =>
    apply typing.app₂
    . apply IHf
    . apply IHarg
  case lit =>
    apply typing.lit
  case lift_lit IH =>
    apply typing.lift_lit
    apply IH
  case code_fragment Hbinds Hwbt =>
    apply typing.code_fragment
    apply Hbinds; apply Hwbt
  case code_rep IH =>
    apply typing.code_rep
    apply IH
  case reflect IH =>
    apply typing.reflect
    apply IH
  case lam𝕔 Hwbt Hclosed IH =>
    apply typing.lam𝕔
    . apply IH
    . apply Hwbt
    . apply Hclosed
  case lets Hwbt Hclosed IHb IHe =>
    apply typing.lets
    . apply IHb
    . apply IHe
    . apply Hwbt
    . apply Hclosed
  case lets𝕔 Hwbt Hclosed IHb IHe =>
    apply typing.lets𝕔
    . apply IHb
    . apply IHe
    . apply Hwbt
    . apply Hclosed
  case run Hclosed IH =>
    apply typing.run
    . apply IH
    . apply Hclosed
  case unit =>
    apply typing.unit
  case loc Hloc =>
    apply typing.loc
    omega
  case alloc₁ IH =>
    apply typing.alloc₁
    apply IH
  case alloc₂ IH =>
    apply typing.alloc₂
    apply IH
  case load₁ IH =>
    apply typing.load₁
    apply IH
  case load₂ IH =>
    apply typing.load₂
    apply IH
  case store₁ IHl IHr =>
    apply typing.store₁
    . apply IHl
    . apply IHr
  case store₂ IHl IHr =>
    apply typing.store₂
    . apply IHl
    . apply IHr
  case pure IH =>
    apply typing_reification.pure
    apply IH
  case reify IH =>
    apply typing_reification.reify
    apply IH
  apply Hτ

theorem typing_reification.weakening.store :
  ∀ σ₀ σ₁ Γ e τ φ,
    σ₀.length ≤ σ₁.length →
    typing_reification σ₀ Γ e τ φ →
    typing_reification σ₁ Γ e τ φ :=
  by
  intros σ₀ σ₁ Γ e τ φ Hσ Hτ
  cases Hτ
  case pure Hτ =>
    apply typing_reification.pure
    apply typing.weakening.store _ _ _ _ _ _ _ Hσ Hτ
  case reify Hτ =>
    apply typing_reification.reify
    apply typing.weakening.store _ _ _ _ _ _ _ Hσ Hτ
