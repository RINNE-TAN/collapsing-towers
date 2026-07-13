import Instar.TwoLevelFinal.LogicalEquiv.Defs

lemma semantics_preservation.erase_ctx𝔼 :
  ∀ E Γ e τ ε k γ₀ γ₁,
    ctx𝔼 E →
    typing Γ 𝟙 E⟦e⟧ τ ε →
    log_approx_env k γ₀ γ₁ (erase_env Γ) →
    (∃ E₀, ctx𝔼 E₀ ∧ (∀ e, msubst γ₀ ⎸E⟦e⟧⎹ = E₀⟦msubst γ₀ ⎸e⎹⟧)) ∧
    (∃ E₁, ctx𝔼 E₁ ∧ (∀ e, msubst γ₁ ⎸E⟦e⟧⎹ = E₁⟦msubst γ₁ ⎸e⎹⟧)) :=
  by
  intros E Γ e τ ε k γ₀ γ₁ HE Hτ HsemΓ
  induction HE generalizing τ ε
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
        . exists (fun X => .app₁ X (msubst γ₀ ⎸arg⎹)) ∘ E₀; simp [IH₀]
          apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.appl₁ _ _) HE₀
          apply lc.under_msubst; apply Hmwf₀
          rw [← lc.under_erase]; apply Hlc
        . exists (fun X => .app₁ X (msubst γ₁ ⎸arg⎹)) ∘ E₁; simp [IH₁]
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
        . exists (fun X => .app₁ (msubst γ₀ ⎸.lam e⎹) X) ∘ E₀; simp [IH₀]
          apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.appr₁ _ _) HE₀
          apply value.lam
          apply lc.under_msubst; apply Hmwf₀
          rw [← lc.under_erase]; apply Hlc
        . exists (fun X => .app₁ (msubst γ₁ ⎸.lam e⎹) X) ∘ E₁; simp [IH₁]
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
        . exists (fun X => .app₁ X (msubst γ₀ ⎸arg⎹)) ∘ E₀; simp [IH₀]
          apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.appl₁ _ _) HE₀
          apply lc.under_msubst; apply Hmwf₀
          rw [← lc.under_erase]; apply Hlc
        . exists (fun X => .app₁ X (msubst γ₁ ⎸arg⎹)) ∘ E₁; simp [IH₁]
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
        . exists (fun X => .binary₁ op X (msubst γ₀ ⎸r⎹)) ∘ E₀; simp [IH₀]
          apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.binaryl₁ _ _ _) HE₀
          apply lc.under_msubst; apply Hmwf₀
          rw [← lc.under_erase]; apply Hlc
        . exists (fun X => .binary₁ op X (msubst γ₁ ⎸r⎹)) ∘ E₁; simp [IH₁]
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
        . exists (fun X => .binary₁ op X (msubst γ₀ ⎸r⎹)) ∘ E₀; simp [IH₀]
          apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.binaryl₁ _ _ _) HE₀
          apply lc.under_msubst; apply Hmwf₀
          rw [← lc.under_erase]; apply Hlc
        . exists (fun X => .binary₁ op X (msubst γ₁ ⎸r⎹)) ∘ E₁; simp [IH₁]
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
        . exists (fun X => .lets X (msubst γ₀ ⎸e⎹)) ∘ E₀; simp [IH₀]
          apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.lets _ _) HE₀
          apply lc.under_msubst; apply Hmwf₀
          rw [← lc.under_erase]; apply Hlc
        . exists (fun X => .lets X (msubst γ₁ ⎸e⎹)) ∘ E₁; simp [IH₁]
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
        . exists (fun X => .store₁ X (msubst γ₀ ⎸r⎹)) ∘ E₀; simp [IH₀]
          apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.storel₁ _ _) HE₀
          apply lc.under_msubst; apply Hmwf₀
          rw [← lc.under_erase]; apply Hlc
        . exists (fun X => .store₁ X (msubst γ₁ ⎸r⎹)) ∘ E₁; simp [IH₁]
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
        . exists (fun X => .ifz₁ X (msubst γ₀ ⎸l⎹) (msubst γ₀ ⎸r⎹)) ∘ E₀; simp [IH₀]
          apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.ifz₁ _ _ _ _) HE₀
          . apply lc.under_msubst; apply Hmwf₀
            rw [← lc.under_erase]; apply Hlcl
          . apply lc.under_msubst; apply Hmwf₀
            rw [← lc.under_erase]; apply Hlcr
        . exists (fun X => .ifz₁ X (msubst γ₁ ⎸l⎹) (msubst γ₁ ⎸r⎹)) ∘ E₁; simp [IH₁]
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
        . exists (fun X => .ifz₁ X (msubst γ₀ ⎸l⎹) (msubst γ₀ ⎸r⎹)) ∘ E₀; simp [IH₀]
          apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.ifz₁ _ _ _ _) HE₀
          . apply lc.under_msubst; apply Hmwf₀
            rw [← lc.under_erase]; apply Hlcl
          . apply lc.under_msubst; apply Hmwf₀
            rw [← lc.under_erase]; apply Hlcr
        . exists (fun X => .ifz₁ X (msubst γ₁ ⎸l⎹) (msubst γ₁ ⎸r⎹)) ∘ E₁; simp [IH₁]
          apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.ifz₁ _ _ _ _) HE₁
          . apply lc.under_msubst; apply Hmwf₁
            rw [← lc.under_erase]; apply Hlcl
          . apply lc.under_msubst; apply Hmwf₁
            rw [← lc.under_erase]; apply Hlcr

-- Γ ⊢ E⟦reflect b⟧ : τ
-- ————————————————————————————————————————————————————————
-- ⎸Γ⎹ ⊨ ⎸E⟦reflect b⟧⎹ ≈𝑙𝑜𝑔 ⎸lets𝕔 x = b in E⟦code x⟧⎹ : ⎸τ⎹
theorem semantics_preservation.reflect.head :
  ∀ Γ E b τ ε,
    ctx𝔼 E →
    typing Γ 𝟙 E⟦.reflect b⟧ τ ε →
    log_equiv (erase_env Γ) ⎸E⟦.reflect b⟧⎹ ⎸.lets𝕔 b E⟦.code (.bvar 0)⟧⎹ (erase_ty τ) :=
  by
  intros Γ E b τ ε HE Hτ₀
  have ⟨τ𝕖, ε₀, ε₁, HEqε, Hτr₀, HτE₀⟩ := preservation.under_ctx𝔼 _ _ _ _ _ HE Hτ₀
  cases Hτr₀
  case reflect τ𝕖 Hτb₀ =>
    have HτE₀ : typing ((.fragment τ𝕖, 𝟙) :: Γ) 𝟙 E⟦.fvar Γ.length⟧ τ ε₁ :=
      by
      rw [← List.singleton_append, ← Effect.pure_union ε₁]
      apply HτE₀
      apply typing.fvar
      . simp
      . simp; apply And.left
        apply typing.dynamic_impl_pure
        apply Hτb₀
    have HEτ₀ := typing.erase.safety _ _ _ _ _ Hτ₀
    have HEτb₀ := typing.erase.safety _ _ _ _ _ Hτb₀
    have HEτE₀ := typing.erase.safety _ _ _ _ _ HτE₀
    have HEτ₁ : typing (erase_env Γ) 𝟚 ⎸.lets𝕔 b E⟦.code (.bvar 0)⟧⎹ (erase_ty τ) ⊥ :=
      by
      simp; rw [← erase.under_ctx𝔼 _ _ HE]; simp
      rw [← Effect.union_pure ⊥]
      apply typing.lets
      . apply HEτb₀
      . rw [← erase_env.length, ← comm.erase_opening, opening.under_ctx𝔼 _ _ _ _ HE]
        apply HEτE₀
      . apply grounded_ty.under_erase
      . rw [← erase_env.length, ← closed.under_erase]
        apply closed.under_ctx𝔼 _ _ _ _ HE
        apply typing.closed_at_env; apply Hτ₀; simp
    constructor
    -- left approximation
    . constructor; apply HEτ₀
      constructor; apply HEτ₁
      intros k 𝓦₀ γ₀ γ₁ HsemΓ
      have ⟨HEq₀, HEq₁⟩ := log_approx_env.length _ _ _ _ _ HsemΓ
      have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.syntactic.mwf _ _ _ _ _ HsemΓ
      have ⟨HmG₀, HmG₁⟩ := log_approx_env.syntactic.mgrounded _ _ _ _ _ HsemΓ
      --
      --
      -- (k, 𝓦₀, γ₀, γ₁) ∈ 𝓖⟦⎸Γ⎹⟧
      -- ————————————————————
      -- γ₀⎸E⟦X⟧⎹ = E₀⟦γ₀⎸X⎹⟧
      -- γ₁⎸E⟦X⟧⎹ = E₁⟦γ₀⎸X⎹⟧
      have ⟨HE₀, HE₁⟩ := semantics_preservation.erase_ctx𝔼 _ _ _ _ _ _ _ _ HE Hτ₀ HsemΓ
      have ⟨E₀, HE₀, HEqE₀⟩ := HE₀
      have ⟨E₁, HE₁, HEqE₁⟩ := HE₁
      have HG₀ : grounded E₀⟦msubst γ₀ ⎸.reflect b⎹⟧ :=
        by
        rw [← HEqE₀ (.reflect b)]
        apply grounded.under_msubst _ _ HmG₀
        apply typing.dynamic_impl_grounded _ _ _ _ HEτ₀
      simp at HG₀
      --
      --
      -- ⟨σ₀, E₀⟦γ₀⎸b⎹⟧⟩ ⭢ ⟦j⟧ ⟨σ₂, v₀⟩
      -- ——————————————————————————————
      -- i₀ + i₁ = j
      -- ⟨σ₀, γ₀⎸b⎹⟩ ⭢ ⟦i₀⟧ ⟨imσ₀, bv₀⟩
      -- ⟨imσ₀, E₀⟦bv₀⟧⟩ ⭢ ⟦i₁⟧ ⟨σ₂, v₀⟩
      simp [HEqE₀, HEqE₁, - log_approx_expr]
      simp only [log_approx_expr]
      intros j Hindexj σ₀ σ₁ Hsem_store σ₂ v₀ Hvalue₀ Hstep₀
      have ⟨imσ₀, i₀, i₁, bv₀, HEqj, HvalueBind₀, HstepBind₀, HstepE₀⟩ := stepn_indexed.refine_at_ctx𝔼 _ _ _ _ _ _ HE₀ Hvalue₀ HG₀ Hstep₀      --
      --
      -- ⟨σ₀, γ₀⎸b⎹⟩ ⭢ ⟦i₀⟧ ⟨imσ₀, bv₀⟩
      -- ⎸Γ⎹ ⊧ ⎸b⎹ ≤𝑙𝑜𝑔 ⎸b⎹ : ⎸τ𝕖⎹
      -- ———————————————————————————————
      -- ⟨σ₁, γ₁⎸b⎹⟩ ⭢* ⟨imσ₁, bv₁⟩
      -- (imσ₀, imσ₁) : 𝓦₁
      -- (k - i₀, 𝓦₁, bv₀, bv₁) ∈ 𝓥⟦⎸τ𝕖⎹⟧
      have ⟨_, _, IHb⟩ := log_approx.fundamental _ _ _ HEτb₀
      simp only [log_approx_expr] at IHb
      have ⟨𝓦₁, imσ₁, bv₁, Hfuture₀, HstepBind₁, Hsem_store, Hsem_value_bind⟩ := IHb _ _ _ _ HsemΓ i₀ (by omega) _ _ Hsem_store _ _ HvalueBind₀ HstepBind₀
      have ⟨_, Hfuture₀⟩ := Hfuture₀
      have ⟨HvalueBind₀, HvalueBind₁⟩ := log_approx_value.syntactic.value _ _ _ _ _ Hsem_value_bind
      have ⟨HwfBind₀, HwfBind₁⟩ := log_approx_value.syntactic.wf _ _ _ _ _ Hsem_value_bind
      --
      --
      -- ⎸Γ⎹ ⊧ ⎸E⟦x⟧⎹ ≤𝑙𝑜𝑔 ⎸E⟦x⟧⎹ : ⎸τ⎹
      -- (k - i₀, 𝓦₁, bv₀, bv₁) ∈ 𝓥⟦⎸τ𝕖⎹⟧
      -- ———————————————————————————————————————————————————————————————
      -- (k - i₀, 𝓦₁, (x ↦ bv₀, γ₀)⎸E⟦x⟧⎹, (x ↦ bv₁, γ₁)⎸E⟦x⟧⎹) ∈ 𝓔⟦⎸τ⎹⟧
      have ⟨_, _, IHE⟩ := log_approx.fundamental _ _ _ HEτE₀
      have Hsem_exprE := IHE (k - i₀) 𝓦₁ (bv₀ :: γ₀) (bv₁ :: γ₁) (
        by
        apply log_approx_env.cons; apply Hsem_value_bind
        apply log_approx_env.antimono; apply HsemΓ
        constructor; omega; apply Hfuture₀
      )
      --
      --
      -- (k - i₀, 𝓦₁, (x ↦ bv₀, γ₀)⎸E⟦x⟧⎹, (x ↦ bv₁, γ₁)⎸E⟦x⟧⎹) ∈ 𝓔⟦⎸τ⎹⟧
      -- ————————————————————————————————————————————————————————————————
      -- (k - i₀, 𝓦₁, E₀⟦bv₀⟧, E₁⟦bv₁⟧) ∈ 𝓔⟦⎸τ⎹⟧
      have HEqE₀ : (msubst (bv₀ :: γ₀) ⎸E⟦.fvar Γ.length⟧⎹) = E₀⟦bv₀⟧:=
        by
        rw [erase_env.length, ← HEq₀]
        rw [msubst, ← comm.msubst_subst _ _ _ _ (by omega) HwfBind₀.right Hmwf₀]
        rw [HEqE₀, subst.under_ctx𝔼 _ _ _ _ _ HE₀]
        simp; apply closed.inc
        rw [← HEqE₀]; apply closed.under_msubst _ _ Hmwf₀
        rw [HEq₀]; apply typing.closed_at_env _ _ _ _ _ HEτ₀; omega
      have HEqE₁ : (msubst (bv₁ :: γ₁) ⎸E⟦.fvar Γ.length⟧⎹) = E₁⟦bv₁⟧:=
        by
        rw [erase_env.length, ← HEq₁]
        rw [msubst, ← comm.msubst_subst _ _ _ _ (by omega) HwfBind₁.right Hmwf₁]
        rw [HEqE₁, subst.under_ctx𝔼 _ _ _ _ _ HE₁]
        simp; apply closed.inc
        rw [← HEqE₁]; apply closed.under_msubst _ _ Hmwf₁
        rw [HEq₁]; apply (typing.closed_at_env _ _ _ _ _ HEτ₁).right; omega
      rw [HEqE₀, HEqE₁] at Hsem_exprE
      --
      --
      -- ⟨imσ₀, E₀⟦bv₀⟧⟩ ⭢ ⟦i₁⟧ ⟨σ₂, v₀⟩
      -- (k - i₀, 𝓦₁, E₀⟦bv₀⟧, E₁⟦bv₁⟧) ∈ 𝓔⟦⎸τ⎹⟧
      -- ———————————————————————————————————————
      -- ⟨imσ₁, E₁⟦bv₁⟧⟩ ⭢* ⟨σ₃, v₁⟩
      -- (σ₂, σ₃) : 𝓦₂
      -- (k - i₀ - i₁, 𝓦₂, v₀, v₁) ∈ 𝓥⟦⎸τ⎹⟧
      simp only [log_approx_expr] at Hsem_exprE
      have ⟨𝓦₂, σ₃, v₁, Hfuture₁, HstepE₁, Hsem_store, Hsem_value⟩ := Hsem_exprE i₁ (by omega) _ _ Hsem_store _ _ Hvalue₀ HstepE₀
      have ⟨_, Hfuture₁⟩ := Hfuture₁
      --
      --
      -- ⟨σ₁, γ₁⎸b⎹⟩ ⭢* ⟨imσ₁, bv₁⟩
      -- ⟨imσ₁, E₁⟦bv₁⟧⟩ ⭢* ⟨σ₃, v₁⟩
      -- —————————————————————————————————————————
      -- ⟨σ₁, lets x = γ₁⎸b⎹ in E₁⟦x⟧⟩ ⭢* ⟨σ₃, v₁⟩
      exists 𝓦₂, σ₃, v₁
      constructor
      . constructor; omega
        apply World.future.trans _ _ _ Hfuture₁
        apply Hfuture₀
      constructor
      . apply stepn.trans
        apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ _ _ (ctx𝔹.lets _ _) _ HstepBind₁
        apply lc.under_ctx𝔼; apply HE₁; simp
        apply grounded.under_msubst _ _ HmG₁; apply typing.dynamic_impl_grounded _ _ _ _ HEτb₀
        apply stepn.multi _ _ _ _ HstepE₁
        apply step_lvl.pure _ _ _ _ ctx𝕄.hole
        . constructor
          . apply lc.value _ HvalueBind₁
          . apply lc.under_ctx𝔼; apply HE₁; simp
        . have HEq : E₁⟦bv₁⟧ = opening 0 bv₁ E₁⟦.bvar 0⟧ :=
            by rw [opening.under_ctx𝔼 _ _ _ _ HE₁]; rfl
          rw [HEq]
          apply head_pure.lets; apply HvalueBind₁
      constructor
      . apply Hsem_store
      . apply log_approx_value.antimono
        apply Hsem_value; simp; omega
    -- right approximation
    . constructor; apply HEτ₁
      constructor; apply HEτ₀
      intros k 𝓦₀ γ₀ γ₁ HsemΓ
      have ⟨HEq₀, HEq₁⟩ := log_approx_env.length _ _ _ _ _ HsemΓ
      have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.syntactic.mwf _ _ _ _ _ HsemΓ
      have ⟨HmG₀, HmG₁⟩ := log_approx_env.syntactic.mgrounded _ _ _ _ _ HsemΓ
      --
      --
      -- (k, 𝓦₀, γ₀, γ₁) ∈ 𝓖⟦⎸Γ⎹⟧
      -- ————————————————————
      -- γ₀⎸E⟦X⟧⎹ = E₀⟦γ₀⎸X⎹⟧
      -- γ₁⎸E⟦X⟧⎹ = E₁⟦γ₀⎸X⎹⟧
      have ⟨HE₀, HE₁⟩ := semantics_preservation.erase_ctx𝔼 _ _ _ _ _ _ _ _ HE Hτ₀ HsemΓ
      have ⟨E₀, HE₀, HEqE₀⟩ := HE₀
      have ⟨E₁, HE₁, HEqE₁⟩ := HE₁
      have HG₀ : grounded (.lets (msubst γ₀ ⎸b⎹) E₀⟦msubst γ₀ ⎸.code (.bvar 0)⎹⟧) :=
        by
        rw [← HEqE₀, ← msubst.lets]
        apply grounded.under_msubst _ _ HmG₀
        apply typing.dynamic_impl_grounded _ _ _ _ HEτ₁
      simp at HG₀
      --
      --
      -- ⟨σ₀, lets x = γ₀⎸b⎹ in γ₀⎸E⟦x⟧⎹⟩ ⭢ ⟦j⟧ ⟨σ₂, v₀⟩
      -- ———————————————————————————————————————————————
      -- i₀ + 1 + i₁ = j
      -- ⟨σ₀, γ₀⎸b⎹⟩ ⭢ ⟦i₀⟧ ⟨imσ₀, bv₀⟩
      -- ⟨imσ₀, E₀⟦bv₀⟧⟩ ⭢ ⟦i₁⟧ ⟨σ₂, v₀⟩
      simp [HEqE₀, HEqE₁, - log_approx_expr]
      simp only [log_approx_expr]
      intros j Hindexj σ₀ σ₁ Hsem_store σ₂ v₀ Hvalue₀ Hstep₀
      have ⟨imσ₀, i₀, i₁, bv₀, HEqj, HvalueBind₀, HstepBind₀, HstepE₀⟩ := stepn_indexed.refine.lets _ _ _ _ _ _ Hvalue₀ HG₀ Hstep₀
      simp [opening.under_ctx𝔼 _ _ _ _ HE₀] at HstepE₀
      --
      --
      -- ⟨σ₀, γ₀⎸b⎹⟩ ⭢ ⟦i₀⟧ ⟨imσ₀, bv₀⟩
      -- ⎸Γ⎹ ⊧ ⎸b⎹ ≤𝑙𝑜𝑔 ⎸b⎹ : ⎸τ𝕖⎹
      -- —————————————————————————————————
      -- ⟨σ₁, γ₁⎸b⎹⟩ ⭢* ⟨imσ₁, bv₁⟩
      -- (imσ₀, imσ₁) : 𝓦₁
      -- (k - i₀, 𝓦₁, bv₀, bv₁) ∈ 𝓥⟦⎸τ𝕖⎹⟧
      have ⟨_, _, IHb⟩ := log_approx.fundamental _ _ _ HEτb₀
      simp only [log_approx_expr] at IHb
      have ⟨𝓦₁, imσ₁, bv₁, Hfuture₀, HstepBind₁, Hsem_store, Hsem_value_bind⟩ := IHb _ _ _ _ HsemΓ i₀ (by omega) _ _ Hsem_store _ _ HvalueBind₀ HstepBind₀
      have ⟨_, Hfuture₀⟩ := Hfuture₀
      have ⟨HvalueBind₀, HvalueBind₁⟩ := log_approx_value.syntactic.value _ _ _ _ _ Hsem_value_bind
      have ⟨HwfBind₀, HwfBind₁⟩ := log_approx_value.syntactic.wf _ _ _ _ _ Hsem_value_bind
      --
      --
      -- ⎸Γ⎹ ⊧ ⎸E⟦x⟧⎹ ≤𝑙𝑜𝑔 ⎸E⟦x⟧⎹ : ⎸τ⎹
      -- (k - i₀, 𝓦₁, bv₀, bv₁) ∈ 𝓥⟦⎸τ𝕖⎹⟧
      -- ———————————————————————————————————————————————————————————————
      -- (k - i₀, 𝓦₁, (x ↦ bv₀, γ₀)⎸E⟦x⟧⎹, (x ↦ bv₁, γ₁)⎸E⟦x⟧⎹) ∈ 𝓔⟦⎸τ⎹⟧
      have ⟨_, _, IHE⟩ := log_approx.fundamental _ _ _ HEτE₀
      have Hsem_exprE := IHE (k - i₀) 𝓦₁ (bv₀ :: γ₀) (bv₁ :: γ₁) (
        by
        apply log_approx_env.cons; apply Hsem_value_bind
        apply log_approx_env.antimono; apply HsemΓ; omega
      )
      --
      --
      -- (k - i₀, 𝓦₁, (x ↦ bv₀, γ₀)⎸E⟦x⟧⎹, (x ↦ bv₁, γ₁)⎸E⟦x⟧⎹) ∈ 𝓔⟦⎸τ⎹⟧
      -- ————————————————————————————————————————————————————————————————
      -- (k - i₀, 𝓦₁, E₀⟦bv₀⟧, E₁⟦bv₁⟧) ∈ 𝓔⟦⎸τ⎹⟧
      have HEqE₀ : (msubst (bv₀ :: γ₀) ⎸E⟦.fvar Γ.length⟧⎹) = E₀⟦bv₀⟧:=
        by
        rw [erase_env.length, ← HEq₀]
        rw [msubst, ← comm.msubst_subst _ _ _ _ (by omega) HwfBind₀.right Hmwf₀]
        rw [HEqE₀, subst.under_ctx𝔼 _ _ _ _ _ HE₀]
        simp; apply closed.inc
        rw [← HEqE₀]; apply closed.under_msubst _ _ Hmwf₀
        rw [HEq₀]; apply typing.closed_at_env _ _ _ _ _ HEτ₀; omega
      have HEqE₁ : (msubst (bv₁ :: γ₁) ⎸E⟦.fvar Γ.length⟧⎹) = E₁⟦bv₁⟧:=
        by
        rw [erase_env.length, ← HEq₁]
        rw [msubst, ← comm.msubst_subst _ _ _ _ (by omega) HwfBind₁.right Hmwf₁]
        rw [HEqE₁, subst.under_ctx𝔼 _ _ _ _ _ HE₁]
        simp; apply closed.inc
        rw [← HEqE₁]; apply closed.under_msubst _ _ Hmwf₁
        rw [HEq₁]; apply (typing.closed_at_env _ _ _ _ _ HEτ₁).right; omega
      rw [HEqE₀, HEqE₁] at Hsem_exprE
      --
      --
      -- ⟨imσ₀, E₀⟦bv₀⟧⟩ ⭢ ⟦i₁⟧ ⟨σ₂, v₀⟩
      -- (k - i₀, 𝓦₁, E₀⟦bv₀⟧, E₁⟦bv₁⟧) ∈ 𝓔⟦⎸τ⎹⟧
      -- ———————————————————————————————————————
      -- ⟨imσ₁, E₁⟦bv₁⟧⟩ ⭢* ⟨σ₃, v₁⟩
      -- (σ₂, σ₃) : 𝓦₂
      -- (k - i₀ - i₁, 𝓦₂, v₀, v₁) ∈ 𝓥⟦⎸τ⎹⟧
      simp only [log_approx_expr] at Hsem_exprE
      have ⟨𝓦₂, σ₃, v₁, Hfuture₁, HstepE₁, Hsem_store, Hsem_value⟩ := Hsem_exprE i₁ (by omega) _ _ Hsem_store _ _ Hvalue₀ HstepE₀
      have ⟨_, Hfuture₁⟩ := Hfuture₁
      --
      --
      -- ⟨σ₁, γ₁⎸b⎹⟩ ⭢* ⟨imσ₁, bv₁⟩
      -- ⟨imσ₁, E₁⟦bv₁⟧⟩ ⭢* ⟨σ₃, v₁⟩
      -- ————————————————————————————
      -- ⟨σ₁, E₁⟦γ₁⎸b⎹⟧⟩ ⭢* ⟨σ₃, v₁⟩
      exists 𝓦₂, σ₃, v₁
      constructor
      . constructor; omega
        apply World.future.trans _ _ _ Hfuture₁
        apply Hfuture₀
      constructor
      . apply stepn.trans _ _ _ _ HstepE₁
        apply stepn_grounded.congruence_under_ctx𝔼 _ _ _ _ _ HE₁ _ HstepBind₁
        apply grounded.under_msubst _ _ HmG₁ (typing.dynamic_impl_grounded _ _ _ _ HEτb₀)
      constructor
      . apply Hsem_store
      . apply log_approx_value.antimono
        apply Hsem_value; simp; omega
