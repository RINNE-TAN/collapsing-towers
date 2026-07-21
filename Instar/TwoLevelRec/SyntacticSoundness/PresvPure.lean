import Instar.TwoLevelRec.SyntacticSoundness.PresvCtx
import Instar.TwoLevelRec.SyntacticSoundness.PresvSubst
import Instar.TwoLevelRec.SyntacticSoundness.PresvOpenSubst

lemma typing.escape.strengthened :
  ∀ Γ e τ ε,
    typing Γ 𝟚 e τ ε →
    typing (escape_env Γ) 𝟙 e τ ε :=
  by
  generalize HEq𝕊 : 𝟚 = 𝕊
  intros Γ e τ ε Hτ
  revert HEq𝕊
  apply
    @typing.rec
      (fun Γ 𝕊 e τ ε (H : typing Γ 𝕊 e τ ε) => 𝟚 = 𝕊 → typing (escape_env Γ) 𝟙 e τ ε)
      (fun Γ e τ ε (H : typing_reification Γ e τ ε) => true)
  <;> (intros; try contradiction)
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
  case binary₁ IHl IHr HEq𝕊 =>
    apply typing.binary₁
    . apply IHl; apply HEq𝕊
    . apply IHr; apply HEq𝕊
  case lets Hwbt Hclosed IHb IHe HEq𝕊 =>
    rw [← HEq𝕊] at Hwbt
    apply typing.lets
    . apply IHb; apply HEq𝕊
    . rw [← escape_env.length, ← escape_env]
      apply IHe; apply HEq𝕊
    . apply wbt.escape _ Hwbt
    . rw [← escape_env.length]
      apply Hclosed
  case fix₁ Hfixε _ IH HEq𝕊 =>
    apply typing.fix₁
    . apply Hfixε
    . apply IH; apply HEq𝕊
  case ifz₁ IHc IHl IHr HEq𝕊 =>
    apply typing.ifz₁
    . apply IHc; apply HEq𝕊
    . apply IHl; apply HEq𝕊
    . apply IHr; apply HEq𝕊
  case pure => simp
  case reify => simp
  apply Hτ

theorem typing.escape :
  ∀ e τ ε,
    typing ⦰ 𝟚 e τ ε →
    typing ⦰ 𝟙 e τ ε :=
  by
  intros e τ ε Hτ
  apply typing.escape.strengthened _ _ _ _ Hτ

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
  case binary₁ =>
    exists ε₀; simp
    cases Hτ
    case binary₁ Hτl Hτr =>
      cases Hτl; cases Hτr; apply typing.lit
  case binary₂ =>
    exists ε₀; simp
    cases Hτ
    case binary₂ Hτ₀ Hτ₁ =>
      cases Hτ₀
      case code_fragment Hwbt₀ Hbinds₀ =>
        cases Hτ₁
        case code_fragment Hwbt₁ Hbinds₁ =>
          apply typing.reflect
          rw [← Effect.union_pure ⊥, ← Effect.union_pure (⊥ ∪ ⊥)]
          apply typing.binary₁
          . apply typing.fvar; apply Hbinds₀; apply Hwbt₀
          . apply typing.fvar; apply Hbinds₁; apply Hwbt₁
  case lift_lit =>
    exists ε₀; simp
    cases Hτ
    case lift_lit Hτ =>
      apply typing.reflect
      apply typing.lit
    case lift_lam => contradiction
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
    case run Hclosed Hτ =>
      rw [← List.append_nil Γ]
      apply typing.weakening
      apply typing.escape
      apply typing.shrinking; simp
      apply typing_reification_code _ _ _ _ Hτ
      apply Hclosed
  case fix₁ Hvalue =>
    exists ε₀; simp
    cases Hτ
    case fix₁ τ𝕒 τ𝕓 ε₁ ε₂ Hfixε Hτf =>
      have Hpure : ε₀ = ⊥ := by cases Hvalue <;> cases Hτf; rfl
      have Hwbt: wbt 𝟙 τ𝕒 := by cases Hvalue <;> cases Hτf; next Hwbt _ => apply Hwbt.left
      rw [Hpure] at Hτf; simp [Hpure]
      apply typing.lam; rw [Hfixε, ← Effect.union_pure (ε₁ ∪ ε₂)]
      apply typing.app₁; apply typing.weakening.singleton; rw [identity.opening, ← Effect.union_pure ε₂, ← Effect.union_pure ε₂]
      apply typing.app₁; apply Hτf
      apply typing.fix₁; apply Hfixε; apply Hτf; constructor; apply Hlc; apply Hlc
      apply typing.fvar; simp
      apply Hwbt; apply Hwbt
      simp; apply typing.closed_at_env _ _ _ _ _ Hτf
  case fix₂ =>
    exists ε₀; simp
    cases Hτ
    case fix₂ Hτ =>
      cases Hτ
      case code_fragment Hwbt Hbinds =>
        apply typing.reflect
        apply typing.fix₁
        . simp; rfl
        . apply typing.fvar; apply Hbinds; apply Hwbt
  case ifz₁_then =>
    cases Hτ
    case ifz₁ ε₀ ε₁ ε₂ Hτc Hτl Hτr =>
      exists ε₁; constructor
      . apply Hτl
      . cases ε₀ <;> cases ε₁ <;> cases ε₂ <;> simp
  case ifz₁_else =>
    cases Hτ
    case ifz₁ ε₀ ε₁ ε₂ Hτc Hτl Hτr =>
      exists ε₂; constructor
      . apply Hτr
      . cases ε₀ <;> cases ε₁ <;> cases ε₂ <;> simp
  case ifz₂ =>
    exists ε₀; simp
    cases Hτ
    case ifz₂ Hτ₀ Hτ₁ Hτ₂ =>
      cases Hτ₀
      case code_fragment Hwbt Hbinds =>
        apply typing.reflect
        rw [← Effect.union_pure ⊥, ← Effect.union_pure (⊥ ∪ ⊥)]
        apply typing.ifz₁
        . apply typing.fvar; apply Hbinds; apply Hwbt
        . apply typing_reification_code _ _ _ _ Hτ₁
        . apply typing_reification_code _ _ _ _ Hτ₂

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
    have Hfv : fv M⟦e₁⟧ ⊆ fv M⟦e₀⟧ := fv.under_ctx𝕄 _ _ _ _ HM (head.fv_shrink _ _ Hhead)
    have ⟨Δ, τ𝕖, ε₁, HEqΓ, Hτ, IHτR⟩ := preservation.under_ctxℝ _ _ _ _ _ _ HR Hlc Hτ
    cases Hτ
    case pure Hτ =>
      have ⟨ε₂, Hτ, HLeε⟩ := IH _ _ _ Hτ HEqΓ
      cases ε₂ <;> try contradiction
      have Hτ := IHτR _ _ Hfv (typing_reification.pure _ _ _ Hτ)
      exists ε₀
    case reify Hτ =>
      have ⟨ε₂, Hτ, HLeε⟩ := IH _ _ _ Hτ HEqΓ
      have Hτ := IHτR _ _ Hfv (typing_reification.reify _ _ _ _ Hτ)
      exists ε₀
