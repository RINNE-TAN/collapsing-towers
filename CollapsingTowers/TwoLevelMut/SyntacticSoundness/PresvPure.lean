import CollapsingTowers.TwoLevelMut.SyntacticSoundness.PresvSubst
import CollapsingTowers.TwoLevelMut.SyntacticSoundness.PresvMaping
import CollapsingTowers.TwoLevelMut.SyntacticSoundness.PresvCtx

lemma typing.escape.strengthened :
  ∀ Γ e τ φ,
    immut e →
    typing Γ 𝟚 e τ φ →
    typing (escape_env Γ) 𝟙 e τ φ :=
  by
  generalize HEq𝕊 : 𝟚 = 𝕊
  intros Γ e τ φ Himmut Hτ
  revert HEq𝕊 Himmut
  apply
    @typing.rec
      (fun Γ 𝕊 e τ φ (H : typing Γ 𝕊 e τ φ) => 𝟚 = 𝕊 → immut e → typing (escape_env Γ) 𝟙 e τ φ)
      (fun Γ e τ φ (H : typing_reification Γ e τ φ) => true)
  <;> (intros; try contradiction)
  case fvar x _ Hbinds Hwbt HEq𝕊 Himmut =>
    rw [← HEq𝕊] at Hwbt
    apply typing.fvar
    . apply escape_env.binds _ _ _ _ Hbinds
    . apply wbt.escape _ Hwbt
  case lam Hwbt Hclosed IH HEq𝕊 Himmut =>
    rw [← HEq𝕊] at Hwbt
    apply typing.lam
    . rw [← escape_env.length, ← escape_env]
      apply IH; apply HEq𝕊
      rw [← immut.under_opening]
      apply Himmut
    . apply wbt.escape _ Hwbt
    . rw [← escape_env.length]
      apply Hclosed
  case app₁ IHf IHarg HEq𝕊 Himmut =>
    apply typing.app₁
    . apply IHf; apply HEq𝕊; apply Himmut.left
    . apply IHarg; apply HEq𝕊; apply Himmut.right
  case lit => apply typing.lit
  case lets Hwbt Hclosed IHb IHe HEq𝕊 Himmut =>
    rw [← HEq𝕊] at Hwbt
    apply typing.lets
    . apply IHb; apply HEq𝕊; apply Himmut.left
    . rw [← escape_env.length, ← escape_env]
      apply IHe; apply HEq𝕊
      rw [← immut.under_opening]
      apply Himmut.right
    . apply wbt.escape _ Hwbt
    . rw [← escape_env.length]
      apply Hclosed
  case unit => apply typing.unit
  case pure => simp
  case reify => simp
  apply Hτ

theorem typing.escape :
  ∀ e τ φ,
    immut e →
    typing ⦰ 𝟚 e τ φ →
    typing ⦰ 𝟙 e τ φ :=
  by
  intros e τ φ Himmut Hτ
  apply typing.escape.strengthened _ _ _ _ Himmut Hτ

theorem preservation.pure.head :
  ∀ Γ e₀ e₁ τ φ₀,
    head_pure e₀ e₁ →
    typing Γ 𝟙 e₀ τ φ₀ →
    ∃ φ₁,
      typing Γ 𝟙 e₁ τ φ₁ ∧
      φ₁ ≤ φ₀ :=
  by
  intros Γ e₀ e₁ τ φ₀ Hhead Hτ
  have Hlc := typing.regular _ _ _ _ _ Hτ
  cases Hhead
  case lets Hvalue =>
    exists φ₀; simp
    cases Hτ
    case lets φ₀ φ₁ _ Hτv Hclosed Hτe =>
      have Hpure : φ₀ = ⊥ := by cases Hvalue <;> cases Hτv <;> rfl
      rw [Hpure] at Hτv; simp [Hpure]
      rw [← intro.subst _ _ _ _ Hclosed]
      apply preservation.subst _ _ _ _ _ _ _ Hτv Hτe
  case app₁ Hvalue =>
    exists φ₀; simp
    cases Hτ
    case app₁ φ₀ φ₁ φ₂ Hτv Hτf =>
      cases Hτf
      case lam Hclosed _ Hτe =>
        have Hpure : φ₂ = ⊥ := by cases Hvalue <;> cases Hτv <;> rfl
        rw [Hpure] at Hτv; simp [Hpure]
        rw [← intro.subst _ _ _ _ Hclosed]
        apply preservation.subst _ _ _ _ _ _ _ Hτv Hτe
  case app₂ =>
    exists φ₀; simp
    cases Hτ
    case app₂ Hτ₀ Hτ₁ =>
      cases Hτ₀
      case code_fragment Hwbt₀ Hbinds₀ =>
        cases Hτ₁
        case code_fragment Hwbt₁ Hbinds₁ =>
          apply typing.reflect
          rw [← Effect.union_pure ⊥, ← Effect.union_pure (⊥ ∪ ⊥)]
          apply typing.app₁
          . apply typing.fvar; apply Hbinds₀; apply Hwbt₀
          . apply typing.fvar; apply Hbinds₁; apply Hwbt₁
  case lift_lit =>
    exists φ₀; simp
    cases Hτ
    case lift_lit Hτ =>
      apply typing.reflect
      apply typing.lit
    case lift_lam => contradiction
    case lift_unit => contradiction
  case lift_lam =>
    exists φ₀; simp
    cases Hτ
    case lift_lam Hτ =>
      cases Hτ
      case lam Hclosed Hwbt Hτe =>
        apply typing.lam𝕔
        . apply typing_reification.reify
          rw [← intro.codify _ _ _ Hclosed, identity.opening_closing]
          apply preservation.maping _ _ _ _ _ _ _ _ Hτe
          apply typing.code_fragment; simp; apply Hwbt
          apply lc.under_subst
          . simp
          . apply typing.regular _ _ _ _ _ Hτe
        . apply Hwbt
        . rw [← closed.under_codify]; apply Hclosed
    case lift_lit => contradiction
    case lift_unit => contradiction
  case lift_unit =>
    exists φ₀; simp
    cases Hτ
    case lift_unit Hτ =>
      apply typing.reflect
      apply typing.unit
    case lift_lit => contradiction
    case lift_lam => contradiction
  case lam𝕔 e =>
    exists φ₀; simp
    cases Hτ
    case lam𝕔 Hwbt Hτ Hclosed =>
      apply typing.reflect
      apply typing.lam
      . apply typing_reification_code _ _ _ _ Hτ
      . apply Hwbt
      . apply Hclosed
  case lets𝕔 b e =>
    exists φ₀; simp
    cases Hτ
    case lets𝕔 Hwbt Hτb Hτe Hclosed =>
      apply typing.code_rep
      rw [← Effect.union_pure ⊥]
      apply typing.lets
      . apply Hτb
      . apply typing_reification_code _ _ _ _ Hτe
      . apply Hwbt
      . apply Hclosed
  case run =>
    exists φ₀; simp
    cases Hτ
    case run Himmut Hclosed Hτ =>
      rw [← List.append_nil Γ]
      apply typing.weakening
      apply typing.escape
      apply Himmut
      apply typing.shrinking; simp
      apply typing_reification_code _ _ _ _ Hτ
      apply Hclosed
  case alloc₂ Hτ =>
    exists φ₀; simp
    cases Hτ
    case alloc₂ Hτ =>
      cases Hτ
      case code_fragment Hwbt Hbinds =>
        apply typing.reflect
        apply typing.alloc₁
        apply typing.fvar; apply Hbinds; apply Hwbt
  case load₂ Hτ =>
    exists φ₀; simp
    cases Hτ
    case load₂ Hτ =>
      cases Hτ
      case code_fragment Hwbt Hbinds =>
        apply typing.reflect
        apply typing.load₁
        apply typing.fvar; apply Hbinds; apply Hwbt
  case store₂ Hτ =>
    exists φ₀; simp
    cases Hτ
    case store₂ Hτ₀ Hτ₁ =>
      cases Hτ₀
      case code_fragment Hwbt₀ Hbinds₀ =>
        cases Hτ₁
        case code_fragment Hwbt₁ Hbinds₁ =>
          apply typing.reflect
          rw [← Effect.union_pure ⊥]
          apply typing.store₁
          . apply typing.fvar; apply Hbinds₀; apply Hwbt₀
          . apply typing.fvar; apply Hbinds₁; apply Hwbt₁

theorem preservation.pure :
  ∀ Γ M e₀ e₁ τ φ₀,
    ctx𝕄 Γ.length M →
    lc e₀ →
    head_pure e₀ e₁ →
    typing Γ 𝟙 M⟦e₀⟧ τ φ₀ →
    ∃ φ₁,
      typing Γ 𝟙 M⟦e₁⟧ τ φ₁ ∧
      φ₁ ≤ φ₀ :=
  by
  intros Γ M e₀ e₁ τ φ₀ HM Hlc Hhead Hτ
  generalize HEqlvl : Γ.length = lvl
  rw [HEqlvl] at HM
  induction HM generalizing Γ τ φ₀
  case hole => apply preservation.pure.head _ _ _ _ _ Hhead Hτ
  case cons𝔹 B M HB HM IH =>
    have ⟨τ𝕖, φ₁, φ₂, HEqφ, Hτ, IHτB⟩ := preservation.under_ctx𝔹 _ _ _ _ _ HB Hτ
    rw [HEqφ]
    have ⟨φ₃, Hτ, HLeφ⟩ := IH _ _ _ Hτ HEqlvl
    have Hτ := IHτB ⦰ _ _ Hτ
    exists φ₃ ∪ φ₂; constructor
    . apply Hτ
    . cases φ₁ <;> cases φ₂ <;> cases φ₃ <;> simp at HLeφ <;> simp
  case consℝ R M HR HM IH =>
    rw [← HEqlvl] at HR IH
    have Hlc : lc M⟦e₀⟧ := lc.under_ctx𝕄 _ _ _ _ HM Hlc
    have Himmut : immut M⟦e₀⟧ → immut M⟦e₁⟧ :=
      by
      intros HimmutM₀
      apply immut.under_ctx𝕄 _ _ _ _ HM HimmutM₀
      apply immut.under_head_pure _ _ Hhead
      apply immut.decompose_ctx𝕄 _ _ _ HM HimmutM₀
    have Hfv : fv M⟦e₁⟧ ⊆ fv M⟦e₀⟧ := fv.under_ctx𝕄 _ _ _ _ HM (head_pure.fv_shrink _ _ Hhead)
    have ⟨Δ, τ𝕖, φ₁, HEqΓ, Hτ, IHτR⟩ := preservation.under_ctxℝ _ _ _ _ _ _ HR Hlc Hτ
    cases Hτ
    case pure Hτ =>
      have ⟨φ₂, Hτ, HLeφ⟩ := IH _ _ _ Hτ HEqΓ
      cases φ₂ <;> try contradiction
      have Hτ := IHτR _ _ Himmut Hfv (typing_reification.pure _ _ _ Hτ)
      exists φ₀
    case reify Hτ =>
      have ⟨φ₂, Hτ, HLeφ⟩ := IH _ _ _ Hτ HEqΓ
      have Hτ := IHτR _ _ Himmut Hfv (typing_reification.reify _ _ _ _ Hτ)
      exists φ₀
