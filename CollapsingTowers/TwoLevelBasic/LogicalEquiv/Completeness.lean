import CollapsingTowers.TwoLevelBasic.CtxEquiv.Defs
import CollapsingTowers.TwoLevelBasic.LogicalEquiv.Fundamental

-- Γ ⊧ e₀ ≈𝑐𝑖𝑢 e₁ : τ ≜
--   Γ ⊢ e₀ : τ ∧
--   Γ ⊢ e₁ : τ ∧
--   ∀ (⦰ ⊢ γ : Γ, ⦰ ⊢ E⟦⦰ ⊢ τ⟧ : ℕ).
--   ∀ v. E⟦γ(e₀)⟧ ⇝* v ↔ E⟦γ(e₁)⟧ ⇝* v
@[simp]
def ciu_equiv (Γ : TEnv) (e₀ e₁: Expr) (τ : Ty) : Prop :=
  typing Γ 𝟚 e₀ τ ⊥ ∧
  typing Γ 𝟚 e₁ τ ⊥ ∧
    ∀ γ, typing.subst γ Γ →
    ∀ E,
      ctx𝔼 E →
      ObsCtxℂ ⦰ τ E ⦰ .nat →
      ∀ v, value v → (
        (E⟦msubst γ e₀⟧ ⇝* v) ↔ (E⟦msubst γ e₁⟧ ⇝* v)
      )

-- Γ ⊧ e₀ ≈𝑐𝑡𝑥 e₁ : τ
-- ——————————————————
-- Γ ⊧ e₀ ≈𝑐𝑖𝑢 e₁ : τ
theorem ctx_equiv_impl_ciu_equiv :
  ∀ Γ τ e₀ e₁,
    ctx_equiv Γ e₀ e₁ τ →
    ciu_equiv Γ e₀ e₁ τ :=
  by
  intros Γ τ e₀ e₁ Hctx
  constructor; apply Hctx.left
  constructor; apply Hctx.right.left
  intros γ Hγ
  induction Hγ generalizing e₀ e₁
  case nil =>
    intros E HE
    apply Hctx.right.right
  case cons argv γ τ𝕒 Γ HvalueArg Hτv Hτγ IH =>
    intros E HE HτE v Hvalue
    have HEq := typing.subst.length _ _ Hτγ
    have HsemΓ := log_equiv_env.refl _ _ Hτγ
    have ⟨Hmwf₀, Hmwf₁⟩ := log_equiv_env.mwf _ _ _ HsemΓ
    have ⟨Hτe₀, Hτe₁, _⟩ := Hctx
    have HEqSubst₀ : msubst γ (subst (List.length Γ) argv e₀) = opening 0 (msubst γ argv) (msubst γ {0 ↤ List.length Γ}e₀) :=
      by
      rw [← comm.msubst_opening_value, ← intro.subst, identity.opening_closing]
      apply typing.regular _ _ _ _ _ Hτe₀
      rw [← closed.under_closing]; apply typing.closed_at_env _ _ _ _ _ Hτe₀
      apply Hmwf₀
    have HEqSubst₁ : msubst γ (subst (List.length Γ) argv e₁) = opening 0 (msubst γ argv) (msubst γ {0 ↤ List.length Γ}e₁) :=
      by
      rw [← comm.msubst_opening_value, ← intro.subst, identity.opening_closing]
      apply typing.regular _ _ _ _ _ Hτe₁
      rw [← closed.under_closing]; apply typing.closed_at_env _ _ _ _ _ Hτe₁
      apply Hmwf₁
    --
    --
    -- (x ↦ τ𝕒, Γ) ⊧ e₀ ≈𝑐𝑡𝑥 e₁ : τ
    -- —————————————————————————————————————
    -- Γ ⊧ λx.e₀ @ argv ≈𝑐𝑡𝑥 λx.e₁ @ argv : τ
    have Hctx : ctx_equiv Γ (.app₁ (.lam {0 ↤ Γ.length}e₀) argv) (.app₁ (.lam {0 ↤ Γ.length}e₁) argv) τ :=
      by
      apply ctx_equiv.congruence_under_ObsCtxℂ _ _ _ _ _ _ _ Hctx
      have ⟨Hwbt, _⟩ := typing.dynamic_impl_pure _ _ _ _ Hτv
      have Hτv := typing.weakening _ Γ _ _ _ _ Hτv
      simp at Hτv
      have HτC := ObsCtxℂ.hole Γ τ
      have HτB := ObsCtx𝔹.appl₁ Γ argv τ𝕒 τ Hτv
      have HτC := ObsCtxℂ.cons𝔹 _ _ _ _ _ _ _ _ HτC HτB
      have HτB := ObsCtx𝔹.lam Γ τ𝕒 τ Hwbt
      apply ObsCtxℂ.cons𝔹 _ _ _ _ _ _ _ _ HτC HτB
    have ⟨Hτ₀, Hτ₁, _⟩ := Hctx
    have ⟨HSτ₀, HSτ₁⟩ := log_equiv_env.msubst.typing _ _ _ _ _ _ Hτ₀ Hτ₁ HsemΓ
    have ⟨Hlc₀, Hclosed₀⟩ := typing.wf _ _ _ _ _ HSτ₀
    have ⟨Hlc₁, Hclosed₁⟩ := typing.wf _ _ _ _ _ HSτ₁
    simp at Hlc₀ Hlc₁ Hclosed₀ Hclosed₁
    have HstepHead₀ : (E⟦msubst γ (.app₁ (.lam {0 ↤ List.length Γ}e₀) argv)⟧ ⇝* E⟦msubst (argv :: γ) e₀⟧) :=
      by
      apply stepn.multi _ _ _ _ (stepn.refl _)
      apply step_grounded.congruence_under_ctx𝔼 _ _ _ HE (typing.dynamic_impl_grounded _ _ _ _ HSτ₀)
      apply step_lvl.pure _ _ _ ctx𝕄.hole
      . simp [Hlc₀]
      . simp [HEq, HEqSubst₀]
        apply head.app₁; rw [identity.msubst]
        apply HvalueArg; apply typing.closed_at_env _ _ _ _ _ Hτv
    have HstepHead₁ : (E⟦msubst γ (.app₁ (.lam {0 ↤ List.length Γ}e₁) argv)⟧ ⇝* E⟦msubst (argv :: γ) e₁⟧) :=
      by
      apply stepn.multi _ _ _ _ (stepn.refl _)
      apply step_grounded.congruence_under_ctx𝔼 _ _ _ HE (typing.dynamic_impl_grounded _ _ _ _ HSτ₁)
      apply step_lvl.pure _ _ _ ctx𝕄.hole
      . simp [Hlc₁]
      . simp [HEq, HEqSubst₁]
        apply head.app₁; rw [identity.msubst]
        apply HvalueArg; apply typing.closed_at_env _ _ _ _ _ Hτv
    have IH := IH _ _ Hctx _ HE HτE v Hvalue
    constructor
    . intros Hstep₀
      have Hstep₀ := stepn.trans _ _ _ HstepHead₀ Hstep₀
      have Hstep₁ := IH.mp Hstep₀
      have ⟨r, Hstepl, Hstepr⟩ := stepn.church_rosser _ _ _ Hstep₁ HstepHead₁
      have HEq := stepn.value_impl_termination _ _ Hvalue Hstepl
      rw [HEq]
      apply Hstepr
    . intros Hstep₁
      have Hstep₁ := stepn.trans _ _ _ HstepHead₁ Hstep₁
      have Hstep₀ := IH.mpr Hstep₁
      have ⟨r, Hstepl, Hstepr⟩ := stepn.church_rosser _ _ _ Hstep₀ HstepHead₀
      have HEq := stepn.value_impl_termination _ _ Hvalue Hstepl
      rw [HEq]
      apply Hstepr

lemma ciu_equiv_respects_log_equiv_value :
  ∀ v₀ v₁ v₂ τ,
    value v₀ → value v₁ → value v₂ →
    log_equiv_value v₀ v₁ τ →
    ciu_equiv ⦰ v₁ v₂ τ →
    log_equiv_value v₀ v₂ τ :=
  by
  intros v₀ v₁ v₂ τ Hvalue₀ Hvalue₁ Hvalue₂ Hsem_value Hciu
  induction τ generalizing v₀ v₁ v₂
  case nat =>
    have ⟨Hτ₁, Hτ₂, Hciu_value⟩ := Hciu
    cases Hvalue₀ <;> try simp at Hsem_value
    case lit n₀ =>
    cases Hvalue₁ <;> try contradiction
    case lit n₁ =>
    cases Hvalue₂ <;> try contradiction
    case lit n₂ =>
    simp at Hsem_value
    have Hciu_value := Hciu_value _ typing.subst.nil _ ctx𝔼.hole (ObsCtxℂ.hole _ _) (.lit n₁) (value.lit _)
    have Hstep₂ := Hciu_value.mp (stepn.refl _)
    have HEqv := stepn.value_impl_termination _ _ (value.lit _) Hstep₂
    simp at HEqv
    simp; omega
  case arrow τ𝕒 τ𝕓 φ IH𝕒 IH𝕓 =>
    have ⟨Hτ₁, Hτ₂, Hciu_value⟩ := Hciu
    cases φ <;> try simp at Hsem_value
    cases Hvalue₀ <;> try simp at Hsem_value
    case lam e₀ Hlc₀ =>
    cases Hvalue₁ <;> try contradiction
    case lam e₁ Hlc₁ =>
    cases Hvalue₂ <;> try contradiction
    case lam e₂ Hlc₂ =>
    simp only [log_equiv_value]
    constructor; simp only [log_equiv_value] at Hsem_value; apply Hsem_value.left
    constructor; apply Hτ₂
    intros argv₀ argv₁ Hsem_value_arg
    have ⟨HvalueArg₀, HvalueArg₁⟩ := log_equiv_value.syntactic.value _ _ _ Hsem_value_arg
    have ⟨HτArg₀, HτArg₁⟩ := log_equiv_value.syntactic.typing _ _ _ Hsem_value_arg
    --
    --
    -- (λx.e₀, λx.e₁) ∈ 𝓥⟦τ𝕒 → τ𝕓⟧
    -- (argv₀, argv₁) ∈ 𝓥⟦τ𝕒⟧
    -- —————————————————————————————————————————
    -- (λx.e₀ @ argv₀, λx.e₁ @ argv₁) ∈ 𝓔⟦τ𝕓⟧
    have Hsem_expr := log_equiv_value.apply _ _ _ _ _ _ Hsem_value Hsem_value_arg
    simp only [log_equiv_expr] at Hsem_expr
    have ⟨v₀, v₁, Hstep₀, Hstep₁, Hsem_value₀⟩ := Hsem_expr
    have ⟨Hvalue₀, Hvalue₁⟩ := log_equiv_value.syntactic.value _ _ _ Hsem_value₀
    have ⟨Hτv₀, Hτv₁⟩ := log_equiv_value.syntactic.typing _ _ _ Hsem_value₀
    --
    --
    -- ⦰ ⊢ λx.e₂ : τ𝕒 → τ𝕓
    -- (argv₀, argv₁) ∈ 𝓥⟦τ𝕒⟧
    -- —————————————————————————————————————————
    -- (λx.e₂ @ argv₀, λx.e₂ @ argv₁) ∈ 𝓔⟦τ𝕓⟧
    have Hsem_expr := log_equiv_value.apply _ _ _ _ _ _ (log_equiv_value.refl _ _ (value.lam _ Hlc₂) Hτ₂) Hsem_value_arg
    simp only [log_equiv_expr] at Hsem_expr
    have ⟨_, v₂, _, Hstep₂, Hsem_value₁⟩ := Hsem_expr
    have ⟨_, Hvalue₂⟩ := log_equiv_value.syntactic.value _ _ _ Hsem_value₁
    have ⟨_, Hτv₂⟩ := log_equiv_value.syntactic.typing _ _ _ Hsem_value₁
    simp only [log_equiv_expr]
    exists v₀, v₂
    constructor; apply Hstep₀
    constructor; apply Hstep₂
    apply IH𝕓 _ _ _ Hvalue₀ Hvalue₁ Hvalue₂ Hsem_value₀
    constructor; apply Hτv₁
    constructor; apply Hτv₂
    intros γ Hγ E HE HτE v Hvalue
    cases γ <;> cases Hγ
    have HstepHead₁ : (E⟦.app₁ (.lam e₁) argv₁⟧ ⇝* E⟦v₁⟧) :=
      by
      apply stepn_grounded.congruence_under_ctx𝔼 _ _ _ HE
      apply typing.dynamic_impl_grounded; apply typing.app₁ _ _ _ _ _ _ _ _ _ Hτ₁ HτArg₁
      apply Hstep₁
    have HstepHead₂ : (E⟦.app₁ (.lam e₂) argv₁⟧ ⇝* E⟦v₂⟧) :=
      by
      apply stepn_grounded.congruence_under_ctx𝔼 _ _ _ HE
      apply typing.dynamic_impl_grounded; apply typing.app₁ _ _ _ _ _ _ _ _ _ Hτ₂ HτArg₁
      apply Hstep₂
    --
    -- ⦰ ⊢ E⟦⦰ ⊢ τ𝕓⟧ : ℕ
    -- ⦰ ⊢ (fun X => X @ argv₁)⟦⦰ ⊢ τ𝕒 → τ𝕓⟧ : τ𝕓
    -- ——————————————————————————————————————————————
    -- ⦰ ⊢ (E ∘ fun X => X @ argv₁)⟦⦰ ⊢ τ𝕒 → τ𝕓⟧ : ℕ
    have HEApp : ctx𝔼 (E ∘ fun X => .app₁ X argv₁) := compose.ctx𝔼_ctx𝔹 _ _ HE (ctx𝔹.appl₁ _ (lc.value _ HvalueArg₁))
    have HτEApp : ObsCtxℂ ⦰ (τ𝕒.arrow τ𝕓 ⊥) (E ∘ fun X => .app₁ X argv₁) ⦰ .nat := ObsCtxℂ.cons𝔹 _ _ _ _ _ _ _ _ HτE (ObsCtx𝔹.appl₁ _ _ _ _ HτArg₁)
    have Hciu_value := Hciu_value _ typing.subst.nil _ HEApp HτEApp v Hvalue
    simp at Hciu_value
    constructor
    . intros Hstep₁
      have Hstep₁ := stepn.trans _ _ _ HstepHead₁ Hstep₁
      have Hstep₂ := Hciu_value.mp Hstep₁
      have ⟨r, Hstepl, Hstepr⟩ := stepn.church_rosser _ _ _ Hstep₂ HstepHead₂
      have HEq := stepn.value_impl_termination _ _ Hvalue Hstepl
      rw [HEq]
      apply Hstepr
    . intros Hstep₂
      have Hstep₂ := stepn.trans _ _ _ HstepHead₂ Hstep₂
      have Hstep₁ := Hciu_value.mpr Hstep₂
      have ⟨r, Hstepl, Hstepr⟩ := stepn.church_rosser _ _ _ Hstep₁ HstepHead₁
      have HEq := stepn.value_impl_termination _ _ Hvalue Hstepl
      rw [HEq]
      apply Hstepr
  case fragment => simp at Hsem_value
  case rep => simp at Hsem_value

-- Γ ⊧ e₀ ≈𝑐𝑖𝑢 e₁ : τ
-- ——————————————————
-- Γ ⊧ e₀ ≈𝑙𝑜𝑔 e₁ : τ
theorem ciu_equiv_impl_log_equiv :
  ∀ Γ τ e₀ e₁,
    ciu_equiv Γ e₀ e₁ τ →
    log_equiv Γ e₀ e₁ τ :=
  by
  intros Γ τ e₀ e₁ Hciu
  admit
