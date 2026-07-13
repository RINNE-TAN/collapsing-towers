import Instar.TwoLevelFinal.SyntacticTyping.Typing

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
    ∀ Γ Ψ Δ Φ 𝕊 e τ ε,
      typing Γ 𝕊 e τ ε →
      Γ = Ψ ++ Φ →
      typing (Ψ ++ Δ ++ Φ) 𝕊 (shiftl Φ.length Δ.length e) τ ε :=
  by
  intros Γ Ψ Δ Φ 𝕊 e τ ε Hτ HEqΓ
  revert Ψ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ ε (H : typing Γ 𝕊 e τ ε) =>
        ∀ Ψ,
          Γ = Ψ ++ Φ →
          typing (Ψ ++ Δ ++ Φ) 𝕊 (shiftl Φ.length Δ.length e) τ ε)
      (fun Γ e τ ε (H : typing_reification Γ e τ ε) =>
        ∀ Ψ,
          Γ = Ψ ++ Φ →
          typing_reification (Ψ ++ Δ ++ Φ) (shiftl Φ.length Δ.length e) τ ε)
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
  case binary₁ IHl IHr Ψ HEqΓ =>
    apply typing.binary₁
    . apply IHl; apply HEqΓ
    . apply IHr; apply HEqΓ
  case binary₂ IHl IHr Ψ HEqΓ =>
    apply typing.binary₂
    . apply IHl; apply HEqΓ
    . apply IHr; apply HEqΓ
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
  case run Hsf Hclosed IH Ψ HEqΓ =>
    apply typing.run
    . apply IH; apply HEqΓ
    . rw [identity.shiftl]; apply Hsf
      apply closed.inc; apply Hclosed; omega
    . rw [identity.shiftl]; apply Hclosed
      apply closed.inc; apply Hclosed; omega
  case unit => apply typing.unit
  case lift_unit IH Ψ HEqΓ =>
    apply typing.lift_unit
    apply IH; apply HEqΓ
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
  case fix₁ Hfixε _ IH Ψ HEqΓ =>
    apply typing.fix₁; apply Hfixε
    apply IH; apply HEqΓ
  case fix₂ IH Ψ HEqΓ =>
    apply typing.fix₂
    apply IH; apply HEqΓ
  case ifz₁ IHc IHl IHr Ψ HEqΓ =>
    apply typing.ifz₁
    . apply IHc; apply HEqΓ
    . apply IHl; apply HEqΓ
    . apply IHr; apply HEqΓ
  case ifz₂ IHc IHl IHr Ψ HEqΓ =>
    apply typing.ifz₂
    . apply IHc; apply HEqΓ
    . apply IHl; apply HEqΓ
    . apply IHr; apply HEqΓ
  case pure IH Ψ HEqΓ =>
    apply typing_reification.pure
    apply IH; apply HEqΓ
  case reify IH Ψ HEqΓ =>
    apply typing_reification.reify
    apply IH; apply HEqΓ
  apply Hτ

theorem typing.weakening :
  ∀ Γ Δ 𝕊 e τ ε,
    typing Γ 𝕊 e τ ε →
    typing (Δ ++ Γ) 𝕊 e τ ε :=
  by
  intros Γ Δ 𝕊 e τ ε Hτ
  rw [← List.nil_append Δ]
  rw [← identity.shiftl _ e]
  apply typing.weakening.strengthened
  apply Hτ; rfl
  apply typing.closed_at_env; apply Hτ

theorem typing.weakening.singleton :
  ∀ Γ Δ 𝕊 e τ ε,
    typing Γ 𝕊 e τ ε ->
    typing (Δ :: Γ) 𝕊 e τ ε :=
  by
  intros Γ Δ 𝕊 e τ
  rw [← List.singleton_append]
  apply typing.weakening

theorem typing_reification.weakening : ∀ Γ Δ e τ ε, typing_reification Γ e τ ε → typing_reification (Δ ++ Γ) e τ ε :=
  by
  intros Γ Δ e τ ε Hτ
  cases Hτ
  case pure Hτ =>
    apply typing_reification.pure
    apply typing.weakening _ _ _ _ _ _ Hτ
  case reify Hτ =>
    apply typing_reification.reify
    apply typing.weakening _ _ _ _ _ _ Hτ
