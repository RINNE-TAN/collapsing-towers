import CollapsingTowers.TwoLevelRec.SyntacticSoundness.PresvCtx
import CollapsingTowers.TwoLevelRec.SyntacticSoundness.PresvSubst
import CollapsingTowers.TwoLevelRec.SyntacticSoundness.PresvMaping

lemma typing.escape.strengthened :
  ∀ Γ e τ φ,
    typing Γ 𝟚 e τ φ →
    typing (escape_env Γ) 𝟙 e τ φ :=
  by
  generalize HEq𝕊 : 𝟚 = 𝕊
  intros Γ e τ φ Hτ
  revert HEq𝕊
  apply
    @typing.rec
      (fun Γ 𝕊 e τ φ (H : typing Γ 𝕊 e τ φ) => 𝟚 = 𝕊 → typing (escape_env Γ) 𝟙 e τ φ)
      (fun Γ e τ φ (H : typing_reification Γ e τ φ) => true)
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
  case fix₁ Hfixφ _ IH HEq𝕊 =>
    apply typing.fix₁
    . apply Hfixφ
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
  ∀ e τ φ,
    typing ⦰ 𝟚 e τ φ →
    typing ⦰ 𝟙 e τ φ :=
  by
  intros e τ φ Hτ
  apply typing.escape.strengthened _ _ _ _ Hτ

theorem preservation.pure.head :
  ∀ Γ e₀ e₁ τ φ₀,
    head e₀ e₁ →
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
  case binary₁ =>
    exists φ₀; simp
    cases Hτ
    case binary₁ Hτl Hτr =>
      cases Hτl; cases Hτr; apply typing.lit
  case binary₂ =>
    exists φ₀; simp
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
    exists φ₀; simp
    cases Hτ
    case lift_lit Hτ =>
      apply typing.reflect
      apply typing.lit
    case lift_lam => contradiction
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
    case run Hclosed Hτ =>
      rw [← List.append_nil Γ]
      apply typing.weakening
      apply typing.escape
      apply typing.shrinking; simp
      apply typing_reification_code _ _ _ _ Hτ
      apply Hclosed
  case fix₁ Hvalue =>
    exists φ₀; simp
    cases Hτ
    case fix₁ τ𝕒 τ𝕓 φ₁ φ₂ Hfixφ Hτf =>
      have Hpure : φ₀ = ⊥ := by cases Hvalue <;> cases Hτf; rfl
      have Hwbt: wbt 𝟙 τ𝕒 := by cases Hvalue <;> cases Hτf; next Hwbt _ => apply Hwbt.left
      rw [Hpure] at Hτf; simp [Hpure]
      apply typing.lam; rw [Hfixφ, ← Effect.union_pure (φ₁ ∪ φ₂)]
      apply typing.app₁; apply typing.weakening.singleton; rw [identity.opening, ← Effect.union_pure φ₂, ← Effect.union_pure φ₂]
      apply typing.app₁; apply Hτf
      apply typing.fix₁; apply Hfixφ; apply Hτf; constructor; apply Hlc; apply Hlc
      apply typing.fvar; simp
      apply Hwbt; apply Hwbt
      simp; apply typing.closed_at_env _ _ _ _ _ Hτf
  case fix₂ =>
    exists φ₀; simp
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
    case ifz₁ φ₀ φ₁ φ₂ Hτc Hτl Hτr =>
      exists φ₁; constructor
      . apply Hτl
      . cases φ₀ <;> cases φ₁ <;> cases φ₂ <;> simp
  case ifz₁_else =>
    cases Hτ
    case ifz₁ φ₀ φ₁ φ₂ Hτc Hτl Hτr =>
      exists φ₂; constructor
      . apply Hτr
      . cases φ₀ <;> cases φ₁ <;> cases φ₂ <;> simp
  case ifz₂ =>
    exists φ₀; simp
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
  ∀ Γ M e₀ e₁ τ φ₀,
    ctx𝕄 Γ.length M →
    lc e₀ →
    head e₀ e₁ →
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
    have Hfv : fv M⟦e₁⟧ ⊆ fv M⟦e₀⟧ := fv.under_ctx𝕄 _ _ _ _ HM (head.fv_shrink _ _ Hhead)
    cases HR
    case lam𝕔 =>
      cases Hτ
      case lam𝕔 Hwbt HX Hclosed =>
        rw [identity.opening_closing _ _ _ Hlc] at HX
        cases HX
        case pure HX =>
          have ⟨φₓ, HX, Hφ⟩ := IH (_ :: Γ) _ _ HX (by simp)
          cases φₓ <;> simp at Hφ
          exists ⊤; constructor
          . apply typing.lam𝕔
            . apply typing_reification.pure
              rw [identity.opening_closing _ _ _ (typing.regular _ _ _ _ _ HX)]
              apply HX
            . apply Hwbt
            . rw [← closed.under_closing]
              apply typing.closed_at_env _ _ _ _ _ HX
          . simp
        case reify HX =>
          have ⟨φₓ, HX, Hφ⟩ := IH (_ :: Γ) _ _ HX (by simp)
          exists ⊤; constructor
          . apply typing.lam𝕔
            . apply typing_reification.reify
              rw [identity.opening_closing _ _ _ (typing.regular _ _ _ _ _ HX)]
              apply HX
            . apply Hwbt
            . rw [← closed.under_closing]
              apply typing.closed_at_env _ _ _ _ _ HX
          . simp
    case lets𝕔 =>
      cases Hτ
      case lets𝕔 Hwbt Hb HX Hclosed =>
        rw [identity.opening_closing _ _ _ Hlc] at HX
        cases HX
        case pure HX =>
          have ⟨φₓ, HX, Hφ⟩ := IH (_ :: Γ) _ _ HX (by simp)
          cases φₓ <;> simp at Hφ
          exists ⊥; constructor
          . apply typing.lets𝕔
            . apply Hb
            . apply typing_reification.pure
              rw [identity.opening_closing _ _ _ (typing.regular _ _ _ _ _ HX)]
              apply HX
            . apply Hwbt
            . rw [← closed.under_closing]
              apply typing.closed_at_env _ _ _ _ _ HX
          . simp
        case reify HX =>
          have ⟨φₓ, HX, Hφ⟩ := IH (_ :: Γ) _ _ HX (by simp)
          exists ⊥; constructor
          . apply typing.lets𝕔
            . apply Hb
            . apply typing_reification.reify
              rw [identity.opening_closing _ _ _ (typing.regular _ _ _ _ _ HX)]
              apply HX
            . apply Hwbt
            . rw [← closed.under_closing]
              apply typing.closed_at_env _ _ _ _ _ HX
          . simp
    case run =>
      cases Hτ
      case run Hclosed HX =>
        cases HX
        case pure HX =>
          have ⟨φₓ, HX, Hφ⟩ := IH _ _ _ HX rfl
          cases φₓ <;> simp at Hφ
          exists ⊥; constructor
          . apply typing.run
            . apply typing_reification.pure _ _ _ HX
            . rw [closed_iff_fv_empty] at Hclosed
              simp [Hclosed] at Hfv
              rw [closed_iff_fv_empty, Hfv]
          . simp
        case reify HX =>
          have ⟨φₓ, HX, Hφ⟩ := IH _ _ _ HX rfl
          exists ⊥; constructor
          . apply typing.run
            . apply typing_reification.reify _ _ _ _ HX
            . rw [closed_iff_fv_empty] at Hclosed
              simp [Hclosed] at Hfv
              rw [closed_iff_fv_empty, Hfv]
          . simp
    case ifzl₂ =>
      cases Hτ
      case ifz₂ Hc HX Hr =>
        cases HX
        case pure HX =>
          have ⟨φₓ, HX, Hφ⟩ := IH _ _ _ HX rfl
          cases φₓ <;> simp at Hφ
          exists ⊤; constructor
          . apply typing.ifz₂; apply Hc; apply typing_reification.pure _ _ _ HX; apply Hr
          . simp
        case reify HX =>
          have ⟨φₓ, HX, Hφ⟩ := IH _ _ _ HX rfl
          exists ⊤; constructor
          . apply typing.ifz₂; apply Hc; apply typing_reification.reify _ _ _ _ HX; apply Hr
          . simp
    case ifzr₂ =>
      cases Hτ
      case ifz₂ Hc Hl HX =>
        cases HX
        case pure HX =>
          have ⟨φₓ, HX, Hφ⟩ := IH _ _ _ HX rfl
          cases φₓ <;> simp at Hφ
          exists ⊤; constructor
          . apply typing.ifz₂; apply Hc; apply Hl; apply typing_reification.pure _ _ _ HX
          . simp
        case reify HX =>
          have ⟨φₓ, HX, Hφ⟩ := IH _ _ _ HX rfl
          exists ⊤; constructor
          . apply typing.ifz₂; apply Hc; apply Hl; apply typing_reification.reify _ _ _ _ HX
          . simp
