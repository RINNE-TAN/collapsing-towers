import Instar.TwoLevelMut.LogicalEquiv.Defs

lemma semantics_preservation.erase_ctx𝔼 :
  ∀ E Γ e τ φ 𝓦 γ₀ γ₁,
    ctx𝔼 E →
    typing Γ 𝟙 E⟦e⟧ τ φ →
    log_equiv_env 𝓦 γ₀ γ₁ (erase_env Γ) →
    (∃ E₀, ctx𝔼 E₀ ∧ (∀ e, msubst γ₀ ‖E⟦e⟧‖ = E₀⟦msubst γ₀ ‖e‖⟧)) ∧
    (∃ E₁, ctx𝔼 E₁ ∧ (∀ e, msubst γ₁ ‖E⟦e⟧‖ = E₁⟦msubst γ₁ ‖e‖⟧)) :=
  by
  intros E Γ e τ φ 𝓦 γ₀ γ₁ HE Hτ HsemΓ
  induction HE generalizing τ φ
  case hole =>
    constructor
    . exists id; constructor; apply ctx𝔼.hole; simp
    . exists id; constructor; apply ctx𝔼.hole; simp
  case cons𝔹 HB HE IH =>
    have ⟨Hmwf₀, Hmwf₁⟩ := log_equiv_env.syntactic.mwf _ _ _ _ HsemΓ
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
          have Hsem_value := log_equiv_env.binds_log_equiv_value _ _ _ _ _ _ HsemΓ Hbinds
          have ⟨Hvalue₀, Hvalue₁⟩ := log_equiv_value.syntactic.value _ _ _ _ Hsem_value
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
          have Hsem_value := log_equiv_env.binds_log_equiv_value _ _ _ _ _ _ HsemΓ Hbinds
          have ⟨Hvalue₀, Hvalue₁⟩ := log_equiv_value.syntactic.value _ _ _ _ Hsem_value
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

-- Γ ⊢ E⟦reflect b⟧ : τ
-- ————————————————————————————————————————————————————————
-- ‖Γ‖ ⊨ ‖E⟦reflect b⟧‖ ≈𝑙𝑜𝑔 ‖lets𝕔 x = b in E⟦code x⟧‖ : ‖τ‖
theorem semantics_preservation.reflect.head :
  ∀ Γ E b τ φ,
    ctx𝔼 E →
    typing Γ 𝟙 E⟦.reflect b⟧ τ φ →
    log_equiv (erase_env Γ) ‖E⟦.reflect b⟧‖ ‖.lets𝕔 b E⟦.code (.bvar 0)⟧‖ (erase_ty τ) :=
  by
  intros Γ E b τ φ HE Hτ₀
  have ⟨τ𝕖, φ₀, φ₁, HEqφ, Hτr₀, HτE₀⟩ := preservation.under_ctx𝔼 _ _ _ _ _ HE Hτ₀
  cases Hτr₀
  case reflect τ𝕖 Hτb₀ =>
    have HτE₀ : typing ((.fragment τ𝕖, 𝟙) :: Γ) 𝟙 E⟦.fvar Γ.length⟧ τ φ₁ :=
      by
      rw [← List.singleton_append, ← Effect.pure_union φ₁]
      apply HτE₀
      apply typing.fvar
      . simp
      . simp; apply And.left
        apply typing.dynamic_impl_pure
        apply Hτb₀
    have HEτ₀ := typing.erase.safety _ _ _ _ _ Hτ₀
    have HEτb₀ := typing.erase.safety _ _ _ _ _ Hτb₀
    have HEτE₀ := typing.erase.safety _ _ _ _ _ HτE₀
    have HEτ₁ : typing (erase_env Γ) 𝟚 ‖.lets𝕔 b E⟦.code (.bvar 0)⟧‖ (erase_ty τ) ⊥ :=
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
    constructor; apply HEτ₀
    constructor; apply HEτ₁
    intros 𝓦₀ γ₀ γ₁ HsemΓ
    have ⟨Hmwf₀, Hmwf₁⟩ := log_equiv_env.syntactic.mwf _ _ _ _ HsemΓ
    have ⟨HmG₀, HmG₁⟩ := log_equiv_env.syntactic.mgrounded _ _ _ _ HsemΓ
    have ⟨HEq₀, HEq₁⟩ := log_equiv_env.length _ _ _ _ HsemΓ
    have HGb₀ : grounded (msubst γ₀ ‖b‖) :=
      by
      apply grounded.under_msubst _ _ HmG₀
      apply typing.dynamic_impl_grounded _ _ _ _ HEτb₀
    have HGb₁ : grounded (msubst γ₁ ‖b‖) :=
      by
      apply grounded.under_msubst _ _ HmG₁
      apply typing.dynamic_impl_grounded _ _ _ _ HEτb₀
    simp only [log_equiv_expr]
    intros σ₀ σ₁ Hsem_store
    --
    --
    -- (γ₀, γ₁) ∈ 𝓖⟦‖Γ‖⟧
    -- ————————————————————
    -- γ₀‖E⟦X⟧‖ = E₀⟦γ₀‖X‖⟧
    -- γ₁‖E⟦X⟧‖ = E₁⟦γ₀‖X‖⟧
    have ⟨HE₀, HE₁⟩ := semantics_preservation.erase_ctx𝔼 _ _ _ _ _ _ _ _ HE Hτ₀ HsemΓ
    have ⟨E₀, HE₀, HEqE₀⟩ := HE₀
    have ⟨E₁, HE₁, HEqE₁⟩ := HE₁
    --
    --
    -- ‖Γ‖ ⊧ ‖b‖ ≈𝑙𝑜𝑔 ‖b‖ : ‖τ𝕖‖
    -- —————————————————————————
    -- 𝓦₁ ⊒ 𝓦₀
    -- ⟨σ₀, γ₀‖b‖⟩ ⭢* ⟨σ₂, bv₀⟩
    -- ⟨σ₁, γ₁‖b‖⟩ ⭢* ⟨σ₃, bv₁⟩
    -- (σ₂, σ₃) : 𝓦₁
    -- (𝓦₁, bv₀, bv₁) ∈ 𝓥⟦‖τ𝕖‖⟧
    have ⟨_, _, IHb⟩ := log_equiv.fundamental _ _ _ HEτb₀
    simp only [log_equiv_expr] at IHb
    have ⟨𝓦₁, σ₂, σ₃, bv₀, bv₁, Hfuture₀, HstepBind₀, HstepBind₁, Hsem_store, Hsem_value_bind⟩ := IHb _ _ _ HsemΓ _ _ Hsem_store
    have ⟨HvalueBind₀, HvalueBind₁⟩ := log_equiv_value.syntactic.value _ _ _ _ Hsem_value_bind
    have ⟨HwfBind₀, HwfBind₁⟩ := log_equiv_value.syntactic.wf _ _ _ _ Hsem_value_bind
    have ⟨HlcBind₀, HclosedBind₀⟩ := HwfBind₀
    have ⟨HlcBind₁, HclosedBind₁⟩ := HwfBind₁
    --
    --
    -- ‖Γ‖ ⊧ ‖E⟦x⟧‖ ≈𝑙𝑜𝑔 ‖E⟦x⟧‖ : ‖τ‖
    -- (𝓦₁, bv₀, bv₁) ∈ 𝓥⟦‖τ𝕖‖⟧
    -- ———————————————————————————————————————————————————————————
    -- 𝓦₂ ⊒ 𝓦₁
    -- ⟨σ₂, (x ↦ bv₀, γ₀)‖E⟦x⟧‖⟩ ⭢* ⟨σ₄, v₀⟩
    -- ⟨σ₃, (x ↦ bv₁, γ₁)‖E⟦x⟧‖⟩ ⭢* ⟨σ₅, v₁⟩
    -- (σ₄, σ₅) : 𝓦₂
    -- (𝓦₂, v₀, v₁) ∈ 𝓔⟦‖τ‖⟧
    have ⟨_, _, IHE⟩ := log_equiv.fundamental _ _ _ HEτE₀
    simp only [log_equiv_expr] at IHE
    have ⟨𝓦₂, σ₄, σ₅, v₀, v₁, Hfuture₁, HstepE₀, HstepE₁, Hsem_store, Hsem_value⟩ :=
      IHE _ _ _ (log_equiv_env.cons _ _ _ _ _ _ _ Hsem_value_bind (log_equiv_env.antimono _ _ _ _ _ HsemΓ Hfuture₀)) _ _ Hsem_store
    --
    --
    exists 𝓦₂, σ₄, σ₅, v₀, v₁
    constructor
    . apply World.future.trans _ _ _ Hfuture₁ Hfuture₀
    constructor
    --
    --
    -- ⟨σ₀, γ₀‖b‖⟩ ⭢* ⟨σ₂, bv₀⟩
    -- ⟨σ₂, (x ↦ bv₀, γ₀)‖E⟦x⟧‖⟩ ⭢* ⟨σ₄, v₀⟩
    -- ——————————————————————————————————————
    -- ⟨σ₀, γ₀‖E⟦b⟧‖⟩ ⭢* ⟨σ₄, v₀⟩
    . simp [HEqE₀]
      have HEqE₀ : (msubst (bv₀ :: γ₀) ‖E⟦.fvar Γ.length⟧‖) = E₀⟦bv₀⟧:=
        by
        rw [erase_env.length, ← HEq₀]
        rw [msubst, ← comm.msubst_subst _ _ _ _ (by omega) HclosedBind₀ Hmwf₀]
        rw [HEqE₀, subst.under_ctx𝔼 _ _ _ _ _ HE₀]
        simp; rw [← HEqE₀]
        apply closed.inc; apply closed.under_msubst _ _ Hmwf₀; simp [HEq₀]
        apply typing.closed_at_env _ _ _ _ _ HEτ₀; omega
      rw [HEqE₀] at HstepE₀
      apply stepn.trans _ _ _ _ HstepE₀
      apply stepn_grounded.congruence_under_ctx𝔼 _ _ _ _ _ HE₀ HGb₀
      apply HstepBind₀
    constructor
    --
    --
    -- ⟨σ₁, γ₁‖b‖⟩ ⭢* ⟨σ₃, bv₁⟩
    -- ⟨σ₃, (x ↦ bv₁, γ₁)‖E⟦x⟧‖⟩ ⭢* ⟨σ₅, v₁⟩
    -- ————————————————————————————————————————————
    -- ⟨σ₁, lets x = γ₁‖b‖ in γ₁‖E⟦x⟧‖⟩ ⭢* ⟨σ₅, v₁⟩
    . simp [HEqE₁]
      have HEqE₁ : (msubst (bv₁ :: γ₁) ‖E⟦.fvar Γ.length⟧‖) = E₁⟦bv₁⟧:=
        by
        rw [erase_env.length, ← HEq₁]
        rw [msubst, ← comm.msubst_subst _ _ _ _ (by omega) HclosedBind₁ Hmwf₁]
        rw [HEqE₁, subst.under_ctx𝔼 _ _ _ _ _ HE₁]
        simp; rw [← HEqE₁]
        apply closed.inc; apply closed.under_msubst _ _ Hmwf₁; simp [HEq₁]
        apply typing.closed_at_env _ _ _ _ _ HEτ₀; omega
      rw [HEqE₁] at HstepE₁
      apply stepn.trans
      apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ _ _ (ctx𝔹.lets _ (lc.under_ctx𝔼 _ _ _ HE₁ (by simp))) HGb₁ HstepBind₁
      apply stepn.multi _ _ _ _ HstepE₁
      apply step_lvl.pure _ _ _ _ ctx𝕄.hole
      . constructor
        . apply HlcBind₁
        . apply lc.under_ctx𝔼; apply HE₁; simp
      . have HEq : E₁⟦bv₁⟧ = opening 0 bv₁ E₁⟦.bvar 0⟧ :=
          by rw [opening.under_ctx𝔼 _ _ _ _ HE₁]; rfl
        rw [HEq]
        apply head_pure.lets; apply HvalueBind₁
    constructor
    . apply Hsem_store
    . apply Hsem_value
