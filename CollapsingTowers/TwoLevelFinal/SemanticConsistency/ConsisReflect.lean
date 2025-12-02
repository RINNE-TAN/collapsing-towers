import CollapsingTowers.TwoLevelFinal.LogicalEquiv.Defs

lemma consistency.erase_ctx𝔼 :
  ∀ E Γ e τ φ k γ₀ γ₁,
    ctx𝔼 E →
    typing Γ 𝟙 E⟦e⟧ τ φ →
    log_approx_env k γ₀ γ₁ (erase_env Γ) →
    (∃ E₀, ctx𝔼 E₀ ∧ (∀ e, msubst γ₀ ‖E⟦e⟧‖ = E₀⟦msubst γ₀ ‖e‖⟧)) ∧
    (∃ E₁, ctx𝔼 E₁ ∧ (∀ e, msubst γ₁ ‖E⟦e⟧‖ = E₁⟦msubst γ₁ ‖e‖⟧)) :=
  by
  intros E Γ e τ φ k γ₀ γ₁ HE Hτ HsemΓ
  induction HE generalizing τ φ
  case hole =>
    constructor
    . exists id; constructor; apply ctx𝔼.hole; simp
    . exists id; constructor; apply ctx𝔼.hole; simp
  case cons𝔹 HB HE IH =>
    have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.syntactic.mwf _ _ _ _ _ HsemΓ
    cases HB <;> try contradiction
    case appl₁ arg Hlc =>
      cases Hτ
      case app₁ Harg HX =>
        have ⟨IH₀, IH₁⟩ := IH _ _ HX
        have ⟨E₀, HE₀, IH₀⟩ := IH₀
        have ⟨E₁, HE₁, IH₁⟩ := IH₁
        constructor
        . exists (fun X => .app₁ X (msubst γ₀ ‖arg‖)) ∘ E₀; simp [IH₀]
          apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.appl₁ _ _) HE₀
          apply lc.under_msubst; apply Hmwf₀
          rw [← lc.under_erase]; apply Hlc
        . exists (fun X => .app₁ X (msubst γ₁ ‖arg‖)) ∘ E₁; simp [IH₁]
          apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.appl₁ _ _) HE₁
          apply lc.under_msubst; apply Hmwf₁
          rw [← lc.under_erase]; apply Hlc
    case appr₁ Hvalue =>
      cases Hvalue <;> try contradiction
      case lam e Hlc =>
      cases Hτ
      case app₁ HX Hf =>
        have ⟨IH₀, IH₁⟩ := IH _ _ HX
        have ⟨E₀, HE₀, IH₀⟩ := IH₀
        have ⟨E₁, HE₁, IH₁⟩ := IH₁
        constructor
        . exists (fun X => .app₁ (msubst γ₀ ‖.lam e‖) X) ∘ E₀; simp [IH₀]
          apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.appr₁ _ _) HE₀
          apply value.lam
          apply lc.under_msubst; apply Hmwf₀
          rw [← lc.under_erase]; apply Hlc
        . exists (fun X => .app₁ (msubst γ₁ ‖.lam e‖) X) ∘ E₁; simp [IH₁]
          apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.appr₁ _ _) HE₁
          apply value.lam
          apply lc.under_msubst; apply Hmwf₁
          rw [← lc.under_erase]; apply Hlc
    case appl₂ arg Hlc =>
      cases Hτ
      case app₂ HX Harg =>
        have ⟨IH₀, IH₁⟩ := IH _ _ HX
        have ⟨E₀, HE₀, IH₀⟩ := IH₀
        have ⟨E₁, HE₁, IH₁⟩ := IH₁
        constructor
        . exists (fun X => .app₁ X (msubst γ₀ ‖arg‖)) ∘ E₀; simp [IH₀]
          apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.appl₁ _ _) HE₀
          apply lc.under_msubst; apply Hmwf₀
          rw [← lc.under_erase]; apply Hlc
        . exists (fun X => .app₁ X (msubst γ₁ ‖arg‖)) ∘ E₁; simp [IH₁]
          apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.appl₁ _ _) HE₁
          apply lc.under_msubst; apply Hmwf₁
          rw [← lc.under_erase]; apply Hlc
    case appr₂ Hvalue =>
      cases Hvalue <;> try contradiction
      case code e Hlc =>
      cases Hτ
      case app₂ Hf HX =>
        cases Hf
        case code_fragment x _ Hbinds =>
          have Hbinds := erase_env.binds _ _ _ _ Hbinds
          have Hsem_value := log_approx_env.binds_log_approx_value _ _ _ _ _ _ _ HsemΓ Hbinds
          have ⟨Hvalue₀, Hvalue₁⟩ := log_approx_value.syntactic.value _ _ _ _ _ Hsem_value
          have ⟨IH₀, IH₁⟩ := IH _ _ HX
          have ⟨E₀, HE₀, IH₀⟩ := IH₀
          have ⟨E₁, HE₁, IH₁⟩ := IH₁
          constructor
          . exists (fun X => .app₁ (msubst γ₀ (.fvar x)) X) ∘ E₀; simp [IH₀]
            apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.appr₁ _ _) HE₀
            apply Hvalue₀
          . exists (fun X => .app₁ (msubst γ₁ (.fvar x)) X) ∘ E₁; simp [IH₁]
            apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.appr₁ _ _) HE₁
            apply Hvalue₁
    case binaryl₁ op r Hlc =>
      cases Hτ
      case binary₁ HX Hr =>
        have ⟨IH₀, IH₁⟩ := IH _ _ HX
        have ⟨E₀, HE₀, IH₀⟩ := IH₀
        have ⟨E₁, HE₁, IH₁⟩ := IH₁
        constructor
        . exists (fun X => .binary₁ op X (msubst γ₀ ‖r‖)) ∘ E₀; simp [IH₀]
          apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.binaryl₁ _ _ _) HE₀
          apply lc.under_msubst; apply Hmwf₀
          rw [← lc.under_erase]; apply Hlc
        . exists (fun X => .binary₁ op X (msubst γ₁ ‖r‖)) ∘ E₁; simp [IH₁]
          apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.binaryl₁ _ _ _) HE₁
          apply lc.under_msubst; apply Hmwf₁
          rw [← lc.under_erase]; apply Hlc
    case binaryr₁ op _ Hvalue =>
      cases Hvalue <;> try contradiction
      case lit n =>
      cases Hτ
      case binary₁ Hl HX =>
        have ⟨IH₀, IH₁⟩ := IH _ _ HX
        have ⟨E₀, HE₀, IH₀⟩ := IH₀
        have ⟨E₁, HE₁, IH₁⟩ := IH₁
        constructor
        . exists (fun X => .binary₁ op (.lit n) X) ∘ E₀; simp [IH₀]
          apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.binaryr₁ _ _ _) HE₀
          apply value.lit
        . exists (fun X => .binary₁ op (.lit n) X) ∘ E₁; simp [IH₁]
          apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.binaryr₁ _ _ _) HE₁
          apply value.lit
    case binaryl₂ op r Hlc =>
      cases Hτ
      case binary₂ HX Hr =>
        have ⟨IH₀, IH₁⟩ := IH _ _ HX
        have ⟨E₀, HE₀, IH₀⟩ := IH₀
        have ⟨E₁, HE₁, IH₁⟩ := IH₁
        constructor
        . exists (fun X => .binary₁ op X (msubst γ₀ ‖r‖)) ∘ E₀; simp [IH₀]
          apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.binaryl₁ _ _ _) HE₀
          apply lc.under_msubst; apply Hmwf₀
          rw [← lc.under_erase]; apply Hlc
        . exists (fun X => .binary₁ op X (msubst γ₁ ‖r‖)) ∘ E₁; simp [IH₁]
          apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.binaryl₁ _ _ _) HE₁
          apply lc.under_msubst; apply Hmwf₁
          rw [← lc.under_erase]; apply Hlc
    case binaryr₂ op _ Hvalue =>
      cases Hvalue <;> try contradiction
      case code e Hlc =>
      cases Hτ
      case binary₂ Hl HX =>
        cases Hl
        case code_fragment x _ Hbinds =>
          have Hbinds := erase_env.binds _ _ _ _ Hbinds
          have Hsem_value := log_approx_env.binds_log_approx_value _ _ _ _ _ _ _ HsemΓ Hbinds
          have ⟨Hvalue₀, Hvalue₁⟩ := log_approx_value.syntactic.value _ _ _ _ _ Hsem_value
          have ⟨IH₀, IH₁⟩ := IH _ _ HX
          have ⟨E₀, HE₀, IH₀⟩ := IH₀
          have ⟨E₁, HE₁, IH₁⟩ := IH₁
          constructor
          . exists (fun X => .binary₁ op (msubst γ₀ (.fvar x)) X) ∘ E₀; simp [IH₀]
            apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.binaryr₁ _ _ _) HE₀
            apply Hvalue₀
          . exists (fun X => .binary₁ op (msubst γ₁ (.fvar x)) X) ∘ E₁; simp [IH₁]
            apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.binaryr₁ _ _ _) HE₁
            apply Hvalue₁
    case lift =>
      cases Hτ
      case lift_lam HX => apply IH _ _ HX
      case lift_lit HX => apply IH _ _ HX
      case lift_unit HX => apply IH _ _ HX
    case lets e Hlc =>
      cases Hτ
      case lets HX Hclosed He =>
        have ⟨IH₀, IH₁⟩ := IH _ _ HX
        have ⟨E₀, HE₀, IH₀⟩ := IH₀
        have ⟨E₁, HE₁, IH₁⟩ := IH₁
        constructor
        . exists (fun X => .lets X (msubst γ₀ ‖e‖)) ∘ E₀; simp [IH₀]
          apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.lets _ _) HE₀
          apply lc.under_msubst; apply Hmwf₀
          rw [← lc.under_erase]; apply Hlc
        . exists (fun X => .lets X (msubst γ₁ ‖e‖)) ∘ E₁; simp [IH₁]
          apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.lets _ _) HE₁
          apply lc.under_msubst; apply Hmwf₁
          rw [← lc.under_erase]; apply Hlc
    case load₂ =>
      cases Hτ
      case load₂ HX =>
        have ⟨IH₀, IH₁⟩ := IH _ _ HX
        have ⟨E₀, HE₀, IH₀⟩ := IH₀
        have ⟨E₁, HE₁, IH₁⟩ := IH₁
        constructor
        . exists (fun X => .load₁ X) ∘ E₀; simp [IH₀]
          apply ctx𝔼.cons𝔹 _ _ ctx𝔹.load₁ HE₀
        . exists (fun X => .load₁ X) ∘ E₁; simp [IH₁]
          apply ctx𝔼.cons𝔹 _ _ ctx𝔹.load₁ HE₁
    case alloc₂ =>
      cases Hτ
      case alloc₂ HX =>
        have ⟨IH₀, IH₁⟩ := IH _ _ HX
        have ⟨E₀, HE₀, IH₀⟩ := IH₀
        have ⟨E₁, HE₁, IH₁⟩ := IH₁
        constructor
        . exists (fun X => .alloc₁ X) ∘ E₀; simp [IH₀]
          apply ctx𝔼.cons𝔹 _ _ ctx𝔹.alloc₁ HE₀
        . exists (fun X => .alloc₁ X) ∘ E₁; simp [IH₁]
          apply ctx𝔼.cons𝔹 _ _ ctx𝔹.alloc₁ HE₁
    case storel₂ r Hlc =>
      cases Hτ
      case store₂ HX Hr =>
        have ⟨IH₀, IH₁⟩ := IH _ _ HX
        have ⟨E₀, HE₀, IH₀⟩ := IH₀
        have ⟨E₁, HE₁, IH₁⟩ := IH₁
        constructor
        . exists (fun X => .store₁ X (msubst γ₀ ‖r‖)) ∘ E₀; simp [IH₀]
          apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.storel₁ _ _) HE₀
          apply lc.under_msubst; apply Hmwf₀
          rw [← lc.under_erase]; apply Hlc
        . exists (fun X => .store₁ X (msubst γ₁ ‖r‖)) ∘ E₁; simp [IH₁]
          apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.storel₁ _ _) HE₁
          apply lc.under_msubst; apply Hmwf₁
          rw [← lc.under_erase]; apply Hlc
    case storer₂ Hvalue =>
      cases Hvalue <;> try contradiction
      case code e Hlc =>
      cases Hτ
      case store₂ Hl HX =>
        cases Hl
        case code_fragment x _ Hbinds =>
          have Hbinds := erase_env.binds _ _ _ _ Hbinds
          have Hsem_value := log_approx_env.binds_log_approx_value _ _ _ _ _ _ _ HsemΓ Hbinds
          have ⟨Hvalue₀, Hvalue₁⟩ := log_approx_value.syntactic.value _ _ _ _ _ Hsem_value
          have ⟨IH₀, IH₁⟩ := IH _ _ HX
          have ⟨E₀, HE₀, IH₀⟩ := IH₀
          have ⟨E₁, HE₁, IH₁⟩ := IH₁
          constructor
          . exists (fun X => .store₁ (msubst γ₀ (.fvar x)) X) ∘ E₀; simp [IH₀]
            apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.storer₁ _ _) HE₀
            apply Hvalue₀
          . exists (fun X => .store₁ (msubst γ₁ (.fvar x)) X) ∘ E₁; simp [IH₁]
            apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.storer₁ _ _) HE₁
            apply Hvalue₁
    case fix₁ =>
      cases Hτ
      case fix₁ HX =>
        have ⟨IH₀, IH₁⟩ := IH _ _ HX
        have ⟨E₀, HE₀, IH₀⟩ := IH₀
        have ⟨E₁, HE₁, IH₁⟩ := IH₁
        constructor
        . exists (fun X => .fix₁ X) ∘ E₀; simp [IH₀]
          apply ctx𝔼.cons𝔹 _ _ ctx𝔹.fix₁ HE₀
        . exists (fun X => .fix₁ X) ∘ E₁; simp [IH₁]
          apply ctx𝔼.cons𝔹 _ _ ctx𝔹.fix₁ HE₁
    case fix₂ =>
      cases Hτ
      case fix₂ HX =>
        have ⟨IH₀, IH₁⟩ := IH _ _ HX
        have ⟨E₀, HE₀, IH₀⟩ := IH₀
        have ⟨E₁, HE₁, IH₁⟩ := IH₁
        constructor
        . exists (fun X => .fix₁ X) ∘ E₀; simp [IH₀]
          apply ctx𝔼.cons𝔹 _ _ ctx𝔹.fix₁ HE₀
        . exists (fun X => .fix₁ X) ∘ E₁; simp [IH₁]
          apply ctx𝔼.cons𝔹 _ _ ctx𝔹.fix₁ HE₁
    case ifz₁ l r Hlcl Hlcr =>
      cases Hτ
      case ifz₁ HX Hl Hr =>
        have ⟨IH₀, IH₁⟩ := IH _ _ HX
        have ⟨E₀, HE₀, IH₀⟩ := IH₀
        have ⟨E₁, HE₁, IH₁⟩ := IH₁
        constructor
        . exists (fun X => .ifz₁ X (msubst γ₀ ‖l‖) (msubst γ₀ ‖r‖)) ∘ E₀; simp [IH₀]
          apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.ifz₁ _ _ _ _) HE₀
          . apply lc.under_msubst; apply Hmwf₀
            rw [← lc.under_erase]; apply Hlcl
          . apply lc.under_msubst; apply Hmwf₀
            rw [← lc.under_erase]; apply Hlcr
        . exists (fun X => .ifz₁ X (msubst γ₁ ‖l‖) (msubst γ₁ ‖r‖)) ∘ E₁; simp [IH₁]
          apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.ifz₁ _ _ _ _) HE₁
          . apply lc.under_msubst; apply Hmwf₁
            rw [← lc.under_erase]; apply Hlcl
          . apply lc.under_msubst; apply Hmwf₁
            rw [← lc.under_erase]; apply Hlcr
    case ifz₂ l r Hlcl Hlcr =>
      cases Hτ
      case ifz₂ HX Hl Hr =>
        have ⟨IH₀, IH₁⟩ := IH _ _ HX
        have ⟨E₀, HE₀, IH₀⟩ := IH₀
        have ⟨E₁, HE₁, IH₁⟩ := IH₁
        constructor
        . exists (fun X => .ifz₁ X (msubst γ₀ ‖l‖) (msubst γ₀ ‖r‖)) ∘ E₀; simp [IH₀]
          apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.ifz₁ _ _ _ _) HE₀
          . apply lc.under_msubst; apply Hmwf₀
            rw [← lc.under_erase]; apply Hlcl
          . apply lc.under_msubst; apply Hmwf₀
            rw [← lc.under_erase]; apply Hlcr
        . exists (fun X => .ifz₁ X (msubst γ₁ ‖l‖) (msubst γ₁ ‖r‖)) ∘ E₁; simp [IH₁]
          apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.ifz₁ _ _ _ _) HE₁
          . apply lc.under_msubst; apply Hmwf₁
            rw [← lc.under_erase]; apply Hlcl
          . apply lc.under_msubst; apply Hmwf₁
            rw [← lc.under_erase]; apply Hlcr

-- Γ ⊢ E⟦reflect b⟧ : τ
-- ————————————————————————————————————————————————————————
-- ‖Γ‖ ⊨ ‖E⟦reflect b⟧‖ ≈𝑙𝑜𝑔 ‖lets𝕔 x = b in E⟦code x⟧‖ : ‖τ‖
theorem consistency.reflect.head :
  ∀ Γ E b τ φ,
    ctx𝔼 E →
    typing Γ 𝟙 E⟦.reflect b⟧ τ φ →
    log_equiv (erase_env Γ) ‖E⟦.reflect b⟧‖ ‖.lets𝕔 b E⟦.code (.bvar 0)⟧‖ (erase_ty τ) :=
  by
  intros Γ E b τ φ HE Hτ₀
  admit
