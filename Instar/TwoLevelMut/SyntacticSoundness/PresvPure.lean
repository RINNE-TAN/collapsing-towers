import Instar.TwoLevelMut.SyntacticSoundness.PresvSubst
import Instar.TwoLevelMut.SyntacticSoundness.PresvOpenSubst
import Instar.TwoLevelMut.SyntacticSoundness.PresvCtx

lemma typing.escape.strengthened :
  ∀ Γ e τ ε,
    store_free e →
    typing Γ 𝟚 e τ ε →
    typing (escape_env Γ) 𝟙 e τ ε :=
  by
  generalize HEq𝕊 : 𝟚 = 𝕊
  intros Γ e τ ε Hsf Hτ
  revert HEq𝕊 Hsf
  apply
    @typing.rec
      (fun Γ 𝕊 e τ ε (H : typing Γ 𝕊 e τ ε) => 𝟚 = 𝕊 → store_free e → typing (escape_env Γ) 𝟙 e τ ε)
      (fun Γ e τ ε (H : typing_reification Γ e τ ε) => true)
  <;> (intros; try contradiction)
  case fvar x _ Hbinds Hwbt HEq𝕊 Hsf =>
    rw [← HEq𝕊] at Hwbt
    apply typing.fvar
    . apply escape_env.binds _ _ _ _ Hbinds
    . apply wbt.escape _ Hwbt
  case lam Hwbt Hclosed IH HEq𝕊 Hsf =>
    rw [← HEq𝕊] at Hwbt
    apply typing.lam
    . rw [← escape_env.length, ← escape_env]
      apply IH; apply HEq𝕊
      rw [← store_free.under_opening]
      apply Hsf
    . apply wbt.escape _ Hwbt
    . rw [← escape_env.length]
      apply Hclosed
  case app₁ IHf IHarg HEq𝕊 Hsf =>
    apply typing.app₁
    . apply IHf; apply HEq𝕊; apply Hsf.left
    . apply IHarg; apply HEq𝕊; apply Hsf.right
  case lit => apply typing.lit
  case lets Hwbt Hclosed IHb IHe HEq𝕊 Hsf =>
    rw [← HEq𝕊] at Hwbt
    apply typing.lets
    . apply IHb; apply HEq𝕊; apply Hsf.left
    . rw [← escape_env.length, ← escape_env]
      apply IHe; apply HEq𝕊
      rw [← store_free.under_opening]
      apply Hsf.right
    . apply wbt.escape _ Hwbt
    . rw [← escape_env.length]
      apply Hclosed
  case unit => apply typing.unit
  case pure => simp
  case reify => simp
  apply Hτ

theorem typing.escape :
  ∀ e τ ε,
    store_free e →
    typing ⦰ 𝟚 e τ ε →
    typing ⦰ 𝟙 e τ ε :=
  by
  intros e τ ε Hsf Hτ
  apply typing.escape.strengthened _ _ _ _ Hsf Hτ

theorem preservation.pure.head :
  ∀ Γ e₀ e₁ τ ε₀,
    e₀ ↝ e₁ →
    typing Γ 𝟙 e₀ τ ε₀ →
    ∃ ε₁,
      typing Γ 𝟙 e₁ τ ε₁ ∧
      ε₁ ≤ ε₀ :=
  by
  intros Γ e₀ e₁ τ ε₀ Hhead Hτ
  have Hlc := typing.regular _ _ _ _ _ Hτ
  cases Hhead
  case lets Hvalue =>
    exists ε₀; simp
    cases Hτ
    case lets ε₀ ε₁ _ Hτv Hclosed Hτe =>
      have Hpure : ε₀ = ⊥ := by cases Hvalue <;> cases Hτv <;> rfl
      rw [Hpure] at Hτv; simp [Hpure]
      rw [← intro.subst _ _ _ _ Hclosed]
      apply preservation.subst _ _ _ _ _ _ _ Hτv Hτe
  case app₁ Hvalue =>
    exists ε₀; simp
    cases Hτ
    case app₁ ε₀ ε₁ ε₂ Hτv Hτf =>
      cases Hτf
      case lam Hclosed _ Hτe =>
        have Hpure : ε₂ = ⊥ := by cases Hvalue <;> cases Hτv <;> rfl
        rw [Hpure] at Hτv; simp [Hpure]
        rw [← intro.subst _ _ _ _ Hclosed]
        apply preservation.subst _ _ _ _ _ _ _ Hτv Hτe
  case app₂ =>
    exists ε₀; simp
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
    exists ε₀; simp
    cases Hτ
    case lift_lit Hτ =>
      apply typing.reflect
      apply typing.lit
    case lift_lam => contradiction
    case lift_unit => contradiction
  case lift_lam =>
    exists ε₀; simp
    cases Hτ
    case lift_lam Hτ =>
      cases Hτ
      case lam Hclosed Hwbt Hτe =>
        apply typing.lam𝕔
        . apply typing_reification.reify
          rw [← intro.codify _ _ _ Hclosed, identity.opening_closing]
          apply preservation.open_subst _ _ _ _ _ _ _ _ Hτe
          apply typing.code_fragment; simp; apply Hwbt
          apply lc.under_subst
          . simp
          . apply typing.regular _ _ _ _ _ Hτe
        . apply Hwbt
        . rw [← closed.under_codify]; apply Hclosed
    case lift_lit => contradiction
    case lift_unit => contradiction
  case lift_unit =>
    exists ε₀; simp
    cases Hτ
    case lift_unit Hτ =>
      apply typing.reflect
      apply typing.unit
    case lift_lit => contradiction
    case lift_lam => contradiction
  case lam𝕔 e =>
    exists ε₀; simp
    cases Hτ
    case lam𝕔 Hwbt Hτ Hclosed =>
      apply typing.reflect
      apply typing.lam
      . apply typing_reification_code _ _ _ _ Hτ
      . apply Hwbt
      . apply Hclosed
  case lets𝕔 b e =>
    exists ε₀; simp
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
    exists ε₀; simp
    cases Hτ
    case run Hsf Hclosed Hτ =>
      rw [← List.append_nil Γ]
      apply typing.weakening
      apply typing.escape
      apply Hsf
      apply typing.shrinking; simp
      apply typing_reification_code _ _ _ _ Hτ
      apply Hclosed
  case alloc₂ Hτ =>
    exists ε₀; simp
    cases Hτ
    case alloc₂ Hτ =>
      cases Hτ
      case code_fragment Hwbt Hbinds =>
        apply typing.reflect
        apply typing.alloc₁
        apply typing.fvar; apply Hbinds; apply Hwbt
  case load₂ Hτ =>
    exists ε₀; simp
    cases Hτ
    case load₂ Hτ =>
      cases Hτ
      case code_fragment Hwbt Hbinds =>
        apply typing.reflect
        apply typing.load₁
        apply typing.fvar; apply Hbinds; apply Hwbt
  case store₂ Hτ =>
    exists ε₀; simp
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
  ∀ Γ M e₀ e₁ τ ε₀,
    ctx𝕄 Γ.length M →
    lc e₀ →
    e₀ ↝ e₁ →
    typing Γ 𝟙 M⟦e₀⟧ τ ε₀ →
    ∃ ε₁,
      typing Γ 𝟙 M⟦e₁⟧ τ ε₁ ∧
      ε₁ ≤ ε₀ :=
  by
  intros Γ M e₀ e₁ τ ε₀ HM Hlc Hhead Hτ
  generalize HEqlvl : Γ.length = lvl
  rw [HEqlvl] at HM
  induction HM generalizing Γ τ ε₀
  case hole => apply preservation.pure.head _ _ _ _ _ Hhead Hτ
  case cons𝔹 B M HB HM IH =>
    have ⟨τ𝕖, ε₁, ε₂, HEqε, Hτ, IHτB⟩ := preservation.under_ctx𝔹 _ _ _ _ _ HB Hτ
    rw [HEqε]
    have ⟨ε₃, Hτ, HLeε⟩ := IH _ _ _ Hτ HEqlvl
    have Hτ := IHτB ⦰ _ _ Hτ
    exists ε₃ ∪ ε₂; constructor
    . apply Hτ
    . cases ε₁ <;> cases ε₂ <;> cases ε₃ <;> simp at HLeε <;> simp
  case consℝ R M HR HM IH =>
    rw [← HEqlvl] at HR IH
    have Hlc : lc M⟦e₀⟧ := lc.under_ctx𝕄 _ _ _ _ HM Hlc
    have Hsf : store_free M⟦e₀⟧ → store_free M⟦e₁⟧ :=
      by
      intros HsfM
      apply store_free.under_ctx𝕄 _ _ _ _ HM HsfM
      apply store_free.under_head_pure _ _ Hhead
      apply store_free.decompose_ctx𝕄 _ _ _ HM HsfM
    have Hfv : fv M⟦e₁⟧ ⊆ fv M⟦e₀⟧ := fv.under_ctx𝕄 _ _ _ _ HM (head_pure.fv_shrink _ _ Hhead)
    have ⟨Δ, τ𝕖, ε₁, HEqΓ, Hτ, IHτR⟩ := preservation.under_ctxℝ _ _ _ _ _ _ HR Hlc Hτ
    cases Hτ
    case pure Hτ =>
      have ⟨ε₂, Hτ, HLeε⟩ := IH _ _ _ Hτ HEqΓ
      cases ε₂ <;> try contradiction
      have Hτ := IHτR _ _ Hsf Hfv (typing_reification.pure _ _ _ Hτ)
      exists ε₀
    case reify Hτ =>
      have ⟨ε₂, Hτ, HLeε⟩ := IH _ _ _ Hτ HEqΓ
      have Hτ := IHτR _ _ Hsf Hfv (typing_reification.reify _ _ _ _ Hτ)
      exists ε₀
