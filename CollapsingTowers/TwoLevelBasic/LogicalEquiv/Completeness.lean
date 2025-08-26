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
    intros E HE HCE v Hvalue
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
    have HstepHead₀ : (E⟦msubst γ (({0 ↤ List.length Γ}e₀).lam.app₁ argv)⟧ ⇝* E⟦msubst (argv :: γ) e₀⟧) :=
      by
      apply stepn.multi _ _ _ _ (stepn.refl _)
      apply step_grounded.congruence_under_ctx𝔼 _ _ _ HE (typing.dynamic_impl_grounded _ _ _ _ HSτ₀)
      apply step_lvl.pure _ _ _ ctx𝕄.hole
      . simp [Hlc₀]
      . simp [HEq, HEqSubst₀]
        apply head.app₁; rw [identity.msubst]
        apply HvalueArg; apply typing.closed_at_env _ _ _ _ _ Hτv
    have HstepHead₁ : (E⟦msubst γ (({0 ↤ List.length Γ}e₁).lam.app₁ argv)⟧ ⇝* E⟦msubst (argv :: γ) e₁⟧) :=
      by
      apply stepn.multi _ _ _ _ (stepn.refl _)
      apply step_grounded.congruence_under_ctx𝔼 _ _ _ HE (typing.dynamic_impl_grounded _ _ _ _ HSτ₁)
      apply step_lvl.pure _ _ _ ctx𝕄.hole
      . simp [Hlc₁]
      . simp [HEq, HEqSubst₁]
        apply head.app₁; rw [identity.msubst]
        apply HvalueArg; apply typing.closed_at_env _ _ _ _ _ Hτv
    have IH := IH _ _ Hctx _ HE HCE v Hvalue
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

-- Γ ⊧ e₀ ≈𝑐𝑖𝑢 e₁ : τ
-- ——————————————————
-- Γ ⊧ e₀ ≈𝑙𝑜𝑔 e₁ : τ
theorem ciu_equiv_impl_log_equiv :
  ∀ Γ τ e₀ e₁,
    ciu_equiv Γ e₀ e₁ τ →
    log_equiv Γ e₀ e₁ τ :=
  by
  intros Γ τ e₀ e₁ Hciu
  induction τ generalizing e₀ e₁
  case nat =>
    have ⟨Hτ₀, Hτ₁, Hciu⟩ := Hciu
    constructor; apply Hτ₀
    constructor; apply Hτ₁
    intros γ₀ γ₁ HsemΓ
    have ⟨Hγ₀, Hγ₁⟩ := log_equiv_env.syntactic.typing _ _ _ HsemΓ
    have ⟨_, _, Hsem_expr⟩ := log_equiv.fundamental _ _ _ Hτ₀
    simp only [log_equiv_expr] at Hsem_expr
    have ⟨v₀, v₁, Hstep₀, Hstep₁, Hsem_value⟩ := Hsem_expr _ _ HsemΓ
    have ⟨Hvalue₀, Hvalue₁⟩ := log_equiv_value.syntactic.value _ _ _ Hsem_value
    have Hstep₂ := (Hciu _ Hγ₁ _ ctx𝔼.hole (ObsCtxℂ.hole _ _) _ Hvalue₁).mp Hstep₁
    simp only [log_equiv_expr]
    exists v₀, v₁
  case arrow τ𝕒 τ𝕓 φ IH𝕒 IH𝕓 =>
    admit
  case fragment =>
    have ⟨Hwbt, _⟩ := typing.dynamic_impl_pure _ _ _ _ Hciu.left
    simp at Hwbt
  case rep =>
    have ⟨Hwbt, _⟩ := typing.dynamic_impl_pure _ _ _ _ Hciu.left
    simp at Hwbt
