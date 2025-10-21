import CollapsingTowers.TwoLevelMut.SyntacticSoundness.PresvSubst
import CollapsingTowers.TwoLevelMut.SyntacticSoundness.PresvMaping
import CollapsingTowers.TwoLevelMut.SyntacticSoundness.PresvCtx

lemma typing.escape.strengthened :
  ∀ σ Γ e τ φ ω,
    typing σ Γ 𝟚 e τ φ ω →
    typing σ (escape_env Γ) 𝟙 e (escape_ty τ) φ (escape_meffects ω) :=
  by
  generalize HEq𝕊 : 𝟚 = 𝕊
  intros σ Γ e τ φ ω Hτ
  revert HEq𝕊
  apply
    @typing.rec σ
      (fun Γ 𝕊 e τ φ ω (H : typing σ Γ 𝕊 e τ φ ω) => 𝟚 = 𝕊 → typing σ (escape_env Γ) 𝟙 e (escape_ty τ) φ (escape_meffects ω))
      (fun Γ e τ φ ω (H : typing_reification σ Γ e τ φ ω) => true)
  <;> intros
  <;> (try contradiction)
  <;> (try simp only [escape_meffects.union, escape_meffects.empty])
  case fvar x _ Hbinds Hwbt HEq𝕊 =>
    rw [← HEq𝕊] at Hwbt
    apply typing.fvar
    . apply escape_env.binds _ _ _ _ Hbinds
    . apply wbt.escape _ Hwbt
  case lam Hwbt Hclosed IH HEq𝕊 =>
    rw [← HEq𝕊] at Hwbt
    apply typing.lam
    . rw [← escape_env.length, ← escape_env]
      apply IH; apply HEq𝕊
    . apply wbt.escape _ Hwbt
    . rw [← escape_env.length]
      apply Hclosed
  case app₁ IHf IHarg HEq𝕊 =>
    apply typing.app₁
    . apply IHf; apply HEq𝕊
    . apply IHarg; apply HEq𝕊
  case lit => apply typing.lit
  case lets Hwbt Hclosed IHb IHe HEq𝕊 =>
    rw [← HEq𝕊] at Hwbt
    apply typing.lets
    . apply IHb; apply HEq𝕊
    . rw [← escape_env.length, ← escape_env]
      apply IHe; apply HEq𝕊
    . apply wbt.escape _ Hwbt
    . rw [← escape_env.length]
      apply Hclosed
  case unit => apply typing.unit
  case alloc₁ IH HEq𝕊 =>
    rw [escape_meffects.init]
    apply typing.alloc₁
    apply IH; apply HEq𝕊
  case load₁ IH HEq𝕊 =>
    rw [escape_meffects.read]
    apply typing.load₁
    apply IH; apply HEq𝕊
  case store₁ IHl IHr HEq𝕊 =>
    rw [escape_meffects.write]
    apply typing.store₁
    . apply IHl; apply HEq𝕊
    . apply IHr; apply HEq𝕊
  apply Hτ

theorem typing.escape :
  ∀ σ e τ φ ω,
    typing σ ⦰ 𝟚 e τ φ ω →
    typing σ ⦰ 𝟙 e (escape_ty τ) φ (escape_meffects ω) :=
  by
  intros σ e τ φ ω Hτ
  apply typing.escape.strengthened _ _ _ _ _ _ Hτ

theorem preservation.pure.head :
  ∀ σ Γ e₀ e₁ τ φ ω,
    head_pure e₀ e₁ →
    typing σ Γ 𝟙 e₀ τ φ ω →
    typing σ Γ 𝟙 e₁ τ φ ω :=
  by
  intros σ Γ e₀ e₁ τ φ ω Hhead Hτ
  have Hlc := typing.regular _ _ _ _ _ _ _ Hτ
  cases Hhead
  case lets Hvalue =>
    cases Hτ
    case lets φ₀ φ₁ ω₀ ω₁ _ Hτv Hclosed Hτe =>
      have Hpureφ : φ₀ = ⊥ := by cases Hvalue <;> cases Hτv <;> rfl
      have Hpureω : ω₀ = ∅ := by cases Hvalue <;> cases Hτv <;> simp at *
      simp [Hpureφ, Hpureω] at Hτv
      simp [Hpureφ, Hpureω]
      rw [← intro.subst _ _ _ _ Hclosed]
      apply preservation.subst _ _ _ _ _ _ _ _ _ Hτv Hτe
  case app₁ Hvalue =>
    cases Hτ
    case app₁ φ₀ φ₁ φ₂ ω₀ ω₁ ω₂ Hτv Hτf =>
      cases Hτf
      case lam Hclosed _ Hτe =>
        have Hpureφ : φ₂ = ⊥ := by cases Hvalue <;> cases Hτv <;> rfl
        have Hpureω : ω₂ = ∅ := by cases Hvalue <;> cases Hτv <;> simp at *
        simp [Hpureφ, Hpureω] at Hτv
        simp [Hpureφ, Hpureω]
        rw [← intro.subst _ _ _ _ Hclosed]
        apply preservation.subst _ _ _ _ _ _ _ _ _ Hτv Hτe
  case app₂ =>
    cases Hτ
    case app₂ Hτ₀ Hτ₁ =>
      cases Hτ₀
      case code_fragment Hwbt₀ Hbinds₀ =>
        cases Hτ₁
        case code_fragment Hwbt₁ Hbinds₁ =>
          apply typing.reflect
          rw [← REffects.union_pure ⊥, ← REffects.union_pure (⊥ ∪ ⊥)]
          apply typing.app₁
          . apply typing.fvar; apply Hbinds₀; apply Hwbt₀
          . apply typing.fvar; apply Hbinds₁; apply Hwbt₁
  case lift_lit =>
    cases Hτ
    case lift_lit Hτ =>
      cases Hτ
      apply typing.reflect
      apply typing.lit
    case lift_lam => contradiction
    case lift_unit => contradiction
  case lift_lam =>
    cases Hτ
    case lift_lam Hτ =>
      cases Hτ
      case lam Hω Hclosed Hwbt Hτe =>
        apply typing.lam𝕔
        . apply typing_reification.reify
          rw [← intro.codify _ _ _ Hclosed, identity.opening_closing]
          apply preservation.maping _ _ _ _ _ _ _ _ _ _ Hτe
          apply typing.code_fragment; simp; apply Hwbt
          apply lc.under_subst
          . simp
          . apply typing.regular _ _ _ _ _ _ _ Hτe
        . apply Hwbt
        . rw [← closed.under_codify]; apply Hclosed
        . apply Hω
    case lift_lit => contradiction
    case lift_unit => contradiction
  case lift_unit =>
    cases Hτ
    case lift_unit Hτ =>
      cases Hτ
      apply typing.reflect
      apply typing.unit
    case lift_lit => contradiction
    case lift_lam => contradiction
  case lam𝕔 e =>
    cases Hτ
    case lam𝕔 Hwbt _ Hτ Hclosed =>
      apply typing.reflect
      apply typing.lam
      . apply typing_reification_code _ _ _ _ _ _ Hτ
      . apply Hwbt
      . apply Hclosed
  case lets𝕔 b e =>
    cases Hτ
    case lets𝕔 Hwbt Hτb Hτe Hclosed =>
      apply typing.code_rep
      rw [← REffects.union_pure ⊥]
      apply typing.lets
      . apply Hτb
      . apply typing_reification_code _ _ _ _ _ _ Hτe
      . apply Hwbt
      . apply Hclosed
  case run =>
    cases Hτ
    case run Hclosed Hτ =>
      rw [← List.append_nil Γ]
      apply typing.weakening
      apply typing.escape
      apply typing.shrinking; simp
      apply typing_reification_code _ _ _ _ _ _ Hτ
      apply Hclosed
  case alloc₂ Hτ =>
    cases Hτ
    case alloc₂ Hτ =>
      cases Hτ
      case code_fragment Hwbt Hbinds =>
        apply typing.reflect
        apply typing.alloc₁
        apply typing.fvar; apply Hbinds; apply Hwbt
  case load₂ Hτ =>
    cases Hτ
    case load₂ Hτ =>
      cases Hτ
      case code_fragment Hwbt Hbinds =>
        apply typing.reflect
        apply typing.load₁
        apply typing.fvar; apply Hbinds; apply Hwbt
  case store₂ Hτ =>
    cases Hτ
    case store₂ Hτ₀ Hτ₁ =>
      cases Hτ₀
      case code_fragment Hwbt₀ Hbinds₀ =>
        cases Hτ₁
        case code_fragment Hwbt₁ Hbinds₁ =>
          apply typing.reflect
          rw [← REffects.union_pure ⊥]
          apply typing.store₁
          . apply typing.fvar; apply Hbinds₀; apply Hwbt₀
          . apply typing.fvar; apply Hbinds₁; apply Hwbt₁

theorem preservation.pure :
  ∀ σ Γ M e₀ e₁ τ φ₀ ω₀,
    ctx𝕄 Γ.length M →
    lc e₀ →
    head_pure e₀ e₁ →
    typing σ Γ 𝟙 M⟦e₀⟧ τ φ₀ ω₀ →
    ∃ φ₁ ω₁,
      typing σ Γ 𝟙 M⟦e₁⟧ τ φ₁ ω₁ ∧
      φ₁ ≤ φ₀ ∧
      ω₁ ≤ ω₀ ∧
      stage_meffects 𝟙 (ω₀ \ ω₁) :=
  by
  intros σ Γ M e₀ e₁ τ φ₀ ω₀ HM Hlc Hhead Hτ
  generalize HEqlvl : Γ.length = lvl
  rw [HEqlvl] at HM
  induction HM generalizing Γ τ φ₀ ω₀
  case hole =>
    exists φ₀, ω₀
    constructor; apply preservation.pure.head _ _ _ _ _ _ _ Hhead Hτ
    constructor; simp
    constructor; simp
    simp
  case cons𝔹 B M HB HM IH =>
    have ⟨τ𝕖, φ₁, φ₂, ω₁, ω₂, HEqφ, HEqω, Hτ, IHτB⟩ := preservation.under_ctx𝔹 _ _ _ _ _ _ _ HB Hτ
    rw [HEqφ, HEqω]
    have ⟨φ₃, ω₃, Hτ, HLeφ, HLeω, Hdiffω⟩ := IH _ _ _ _ Hτ HEqlvl
    have Hτ := IHτB σ ⦰ _ _ _ (by omega) Hτ
    exists φ₃ ∪ φ₂, ω₃ ∪ ω₂; constructor
    . apply Hτ
    . constructor; cases φ₁ <;> cases φ₂ <;> cases φ₃ <;> simp at HLeφ <;> simp
      constructor; apply Set.union_subset_union_left _ HLeω
      apply stage_meffects.mono _ _ _ _ Hdiffω
      apply Set.union_diff_union_cancel_right
  case consℝ R M HR HM IH =>
    rw [← HEqlvl] at HR IH
    have Hlc : lc M⟦e₀⟧ := lc.under_ctx𝕄 _ _ _ _ HM Hlc
    have Hfv : fv M⟦e₁⟧ ⊆ fv M⟦e₀⟧ := fv.under_ctx𝕄 _ _ _ _ HM (head_pure.fv_shrink _ _ Hhead)
    have ⟨Δ, τ𝕖, φ₁, ω₁, HEqΓ, Hτ, IHτR⟩ := preservation.under_ctxℝ _ _ _ _ _ _ _ _ HR Hlc Hτ
    cases Hτ
    case pure Hτ =>
      have ⟨φ₂, ω₂, Hτ, HLeφ, HLeω, Hdiffω⟩ := IH _ _ _ _ Hτ HEqΓ
      cases φ₂ <;> try contradiction
      have ⟨ω₃, HLeω, Hdiffω, Hτ⟩ := IHτR σ _ _ _ (by simp) Hfv HLeω Hdiffω (typing_reification.pure _ _ _ _ _ Hτ)
      exists φ₀, ω₃
    case reify Hτ =>
      have ⟨φ₂, ω₂, Hτ, HLeφ, HLeω, Hdiffω⟩ := IH _ _ _ _ Hτ HEqΓ
      have ⟨ω₃, HLeω, Hdiffω, Hτ⟩ := IHτR σ _ _ _ (by simp) Hfv HLeω Hdiffω (typing_reification.reify _ _ _ _ _ _ Hτ)
      exists φ₀, ω₃
