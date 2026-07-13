import Instar.TwoLevelRec.CtxEquiv.Defs
import Instar.TwoLevelRec.LogicalEquiv.Fundamental

-- Γ ⊧ e₀ ≤𝑐𝑖𝑢 e₁ : τ ≜
--   Γ ⊢ e₀ : τ ∧
--   Γ ⊢ e₁ : τ ∧
--   ∀ (⦰ ⊢ γ : Γ, ⦰ ⊢ E⟦⦰ ⊢ τ⟧ : τ𝕖).
--   E⟦γ(e₀)⟧⇓ → E⟦γ(e₁)⟧⇓
@[simp]
def ciu_approx (Γ : TEnv) (e₀ e₁: Expr) (τ : Ty) : Prop :=
  typing Γ 𝟚 e₀ τ ⊥ ∧
  typing Γ 𝟚 e₁ τ ⊥ ∧
    ∀ γ, typing.subst γ Γ →
    ∀ E τ𝕖,
      ctx𝔼 E →
      ObsCtxℂ ⦰ τ E ⦰ τ𝕖 →
      termination E⟦msubst γ e₀⟧ →
      termination E⟦msubst γ e₁⟧

-- Γ ⊧ e₀ ≤𝑐𝑡𝑥 e₁ : τ
-- ——————————————————
-- Γ ⊧ e₀ ≤𝑐𝑖𝑢 e₁ : τ
theorem ctx_approx_impl_ciu_approx :
  ∀ Γ τ e₀ e₁,
    ctx_approx Γ e₀ e₁ τ →
    ciu_approx Γ e₀ e₁ τ :=
  by
  intros Γ τ e₀ e₁ Hctx
  constructor; apply Hctx.left
  constructor; apply Hctx.right.left
  intros γ Hγ
  induction Hγ generalizing e₀ e₁
  case nil =>
    intros E τ𝕖 HE
    apply Hctx.right.right
  case cons argv γ τ𝕒 Γ HvalueArg Hτv Hτγ IH =>
    intros E τ𝕖 HE HτE Htermination₀
    have HEq := typing.subst.length _ _ Hτγ
    have HsemΓ := log_approx_env.refl 0 _ _ Hτγ
    have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.mwf _ _ _ _ HsemΓ
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
    -- (x ↦ τ𝕒, Γ) ⊧ e₀ ≤𝑐𝑡𝑥 e₁ : τ
    -- ————————————————————————————————
    -- Γ ⊧ λx.e₀ @ argv ≤𝑐𝑡𝑥 λx.e₁ @ argv : τ
    have Hctx : ctx_approx Γ (.app₁ (.lam {0 ↤ Γ.length}e₀) argv) (.app₁ (.lam {0 ↤ Γ.length}e₁) argv) τ :=
      by
      apply ctx_approx.congruence_under_ObsCtxℂ _ _ _ _ _ _ _ Hctx
      have ⟨Hwbt, _⟩ := typing.dynamic_impl_pure _ _ _ _ Hτv
      have Hτv := typing.weakening _ Γ _ _ _ _ Hτv
      simp at Hτv
      have HτC := ObsCtxℂ.hole Γ τ
      have HτB := ObsCtx𝔽.appl₁ Γ argv τ𝕒 τ Hτv
      have HτC := ObsCtxℂ.cons𝔽 _ _ _ _ _ _ _ _ HτC HτB
      have HτB := ObsCtx𝔽.lam Γ τ𝕒 τ Hwbt
      apply ObsCtxℂ.cons𝔽 _ _ _ _ _ _ _ _ HτC HτB
    have ⟨Hτ₀, Hτ₁, _⟩ := Hctx
    have ⟨HSτ₀, HSτ₁⟩ := log_approx_env.msubst.typing _ _ _ _ _ _ _ Hτ₀ Hτ₁ HsemΓ
    have HSτE₀ := typing.congruence_under_ObsCtxℂ _ _ _ _ _ _ HSτ₀ HτE
    have HSτE₁ := typing.congruence_under_ObsCtxℂ _ _ _ _ _ _ HSτ₁ HτE
    have ⟨Hlc₀, Hclosed₀⟩ := typing.wf _ _ _ _ _ HSτ₀
    have ⟨Hlc₁, Hclosed₁⟩ := typing.wf _ _ _ _ _ HSτ₁
    simp at Hlc₀ Hlc₁ Hclosed₀ Hclosed₁
    --
    --
    -- E⟦(x ↦ argv, γ)e₀⟧⇓
    -- ———————————————————
    -- E⟦λx.γ(e₀) @ argv⟧⇓
    have Htermination₀ : termination E⟦msubst γ (({0 ↤ List.length Γ}e₀).lam.app₁ argv)⟧ :=
      by
      have ⟨v₀, Hvalue₀, Hstep₀⟩ := Htermination₀
      exists v₀
      constructor
      . apply Hvalue₀
      . apply stepn.multi _ _ _ _ Hstep₀
        apply step_grounded.congruence_under_ctx𝔼 _ _ _ HE (typing.dynamic_impl_grounded _ _ _ _ HSτ₀)
        apply step_lvl.pure _ _ _ ctx𝕄.hole
        . simp [Hlc₀]
        . simp [HEq, HEqSubst₀]
          apply head.app₁; rw [identity.msubst]
          apply HvalueArg; apply typing.closed_at_env _ _ _ _ _ Hτv
    --
    --
    -- E⟦λx.γ(e₁) @ argv⟧⇓
    -- ———————————————————
    -- E⟦(x ↦ argv, γ)e₁⟧⇓
    have ⟨v₁, Hvalue₁, Hstep₁⟩ := IH _ _ Hctx _ _ HE HτE Htermination₀
    exists v₁
    constructor
    . apply Hvalue₁
    . have ⟨j, Hstep₁⟩ := stepn_impl_stepn_indexed _ _ Hstep₁
      have ⟨_, _, v𝕖, _, Hvalue𝕖, Hstep𝕖₁, HstepE₁⟩ := stepn_indexed.refine_at_ctx𝔼 _ _ _ _ HE Hvalue₁ (typing.dynamic_impl_grounded _ _ _ _ HSτE₁) Hstep₁
      simp at Hstep𝕖₁
      have HvalueFun : value (msubst γ {0 ↤ List.length Γ}e₁).lam := value.lam _ Hlc₁.left
      have HvalueArg : value (msubst γ argv) := by rw [identity.msubst _ _ (typing.closed_at_env _ _ _ _ _ Hτv)]; apply HvalueArg
      have ⟨_, _, Hstep𝕖₁⟩ := stepn_indexed.refine.app₁.eliminator _ _ _ _ HvalueFun HvalueArg Hvalue𝕖 Hstep𝕖₁
      have Hstep𝕖₁ := stepn_indexed_impl_stepn _ _ _ Hstep𝕖₁
      have HstepE₁ := stepn_indexed_impl_stepn _ _ _ HstepE₁
      apply stepn.trans _ _ _ _ HstepE₁
      simp [HEq, HEqSubst₁]
      apply stepn_grounded.congruence_under_ctx𝔼 _ _ _ HE (
        by
        have HG₁ := typing.dynamic_impl_grounded _ _ _ _ HSτ₁
        simp at HG₁
        apply grounded.under_opening_value
        . apply HG₁.right
        . apply HG₁.left
      ) Hstep𝕖₁

lemma ciu_approx_respects_log_approx_value :
  ∀ k v₀ v₁ v₂ τ,
    value v₀ → value v₁ → value v₂ →
    log_approx_value k v₀ v₁ τ →
    ciu_approx ⦰ v₁ v₂ τ →
    log_approx_value k v₀ v₂ τ :=
  by
  intros k v₀ v₁ v₂ τ Hvalue₀ Hvalue₁ Hvalue₂ Hsem_value Hciu
  induction τ generalizing k v₀ v₁ v₂
  case nat =>
    have ⟨Hτ₁, Hτ₂, Hciu_value⟩ := Hciu
    cases Hvalue₀ <;> try simp at Hsem_value
    case lit n₀ =>
    cases Hvalue₁ <;> try contradiction
    case lit n₁ =>
    cases Hvalue₂ <;> try contradiction
    case lit n₂ =>
    simp at Hsem_value
    cases Hn : compare n₁ n₂ with
    | eq =>
      rw [compare_eq_iff_eq] at Hn
      simp [Hsem_value, Hn]
    | lt =>
      exfalso; apply divergence
      rw [compare_lt_iff_lt] at Hn
      --
      --
      -- n₁ < n₂
      -- E = fun X => if (X - n₁) then 0 else diverge
      -- —————————————————————————————————————————————
      -- E⟦n₁⟧ ⭢* 0
      -- E⟦n₂⟧ ⭢* diverge
      -- ⦰ ⊢ E⟦⦰ ⊢ ℕ⟧ : ℕ
      have Hstep₁ : ((.ifz₁ (.binary₁ .sub (.lit n₁) (.lit n₁)) (.lit 0) diverge) ⭢* (.lit 0)) :=
        by
        -- head sub
        apply stepn.multi
        apply step_lvl.pure (fun X => .ifz₁ X (.lit 0) diverge)
        . apply ctx𝕄.cons𝔹 _ _ (ctx𝔹.ifz₁ _ _ (by simp) (typing.regular _ _ _ _ _ typing_diverge)) ctx𝕄.hole
        . simp
        . apply head.binary₁
        -- head if then
        apply stepn.multi _ _ _ _ (stepn.refl _)
        apply step_lvl.pure _ _ _ ctx𝕄.hole
        . simp; apply typing.regular _ _ _ _ _ typing_diverge
        . simp; apply head.ifz₁_then
      have Hstep₂ : ((.ifz₁ (.binary₁ .sub (.lit n₂) (.lit n₁)) (.lit 0) diverge) ⭢* diverge) :=
        by
        -- head sub
        apply stepn.multi
        apply step_lvl.pure (fun X => .ifz₁ X (.lit 0) diverge)
        . apply ctx𝕄.cons𝔹 _ _ (ctx𝔹.ifz₁ _ _ (by simp) (typing.regular _ _ _ _ _ typing_diverge)) ctx𝕄.hole
        . simp
        . apply head.binary₁
        -- head if else
        apply stepn.multi _ _ _ _ (stepn.refl _)
        apply step_lvl.pure _ _ _ ctx𝕄.hole
        . simp; apply typing.regular _ _ _ _ _ typing_diverge
        . have ⟨n, HEqn⟩ : ∃ n, n₂ - n₁ = n + 1 := by exists n₂ - n₁ - 1; omega
          simp [HEqn]
          apply head.ifz₁_else
      have HE : ctx𝔼 (fun X => .ifz₁ (.binary₁ .sub X (.lit n₁)) (.lit 0) diverge) :=
        by
        apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.ifz₁ _ _ (by simp) (typing.regular _ _ _ _ _ typing_diverge))
        apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.binaryl₁ _ _ (by simp))
        apply ctx𝔼.hole
      have HτE : ObsCtxℂ ⦰ .nat (fun X => .ifz₁ (.binary₁ .sub X (.lit n₁)) (.lit 0) diverge) ⦰ .nat :=
        by
        have HτC := ObsCtxℂ.hole ⦰ .nat
        have HτB := ObsCtx𝔽.ifz₁ _ _ _ _ (typing.lit _ _ 0) typing_diverge
        have HτC := ObsCtxℂ.cons𝔽 _ _ _ _ _ _ _ _ HτC HτB
        have HτB := ObsCtx𝔽.binaryl₁ ⦰ .sub _ (typing.lit _ _ n₁)
        apply ObsCtxℂ.cons𝔽 _ _ _ _ _ _ _ _ HτC HτB
      --
      --
      -- E⟦n₁⟧⇓
      -- ⦰ ⊧ n₁ ≤𝑐𝑖𝑢 n₂ : ℕ
      -- ——————————————————
      -- E⟦n₂⟧⇓
      have Htermination := Hciu_value _ typing.subst.nil _ _ HE HτE (by exists .lit 0)
      --
      --
      -- E⟦n₂⟧⇓
      -- E⟦n₂⟧ ⭢* diverge
      -- ——————————————————
      -- diverge⇓
      rw [← termination.under_stepn]
      apply Htermination
      apply Hstep₂
    | gt =>
      exfalso; apply divergence
      rw [compare_gt_iff_gt] at Hn
      --
      --
      -- n₁ > n₂
      -- E = fun X => if (X - n₂) then diverge else 0
      -- —————————————————————————————————————————————
      -- E⟦n₁⟧ ⭢* 0
      -- E⟦n₂⟧ ⭢* diverge
      -- ⦰ ⊢ E⟦⦰ ⊢ ℕ⟧ : ℕ
      have Hstep₁ : ((.ifz₁ (.binary₁ .sub (.lit n₁) (.lit n₂)) diverge (.lit 0)) ⭢* (.lit 0)) :=
        by
        -- head sub
        apply stepn.multi
        apply step_lvl.pure (fun X => .ifz₁ X diverge (.lit 0))
        . apply ctx𝕄.cons𝔹 _ _ (ctx𝔹.ifz₁ _ _ (typing.regular _ _ _ _ _ typing_diverge) (by simp)) ctx𝕄.hole
        . simp
        . apply head.binary₁
        -- head if then
        apply stepn.multi _ _ _ _ (stepn.refl _)
        apply step_lvl.pure _ _ _ ctx𝕄.hole
        . simp; apply typing.regular _ _ _ _ _ typing_diverge
        . have ⟨n, HEqn⟩ : ∃ n, n₁ - n₂ = n + 1 := by exists n₁ - n₂ - 1; omega
          simp [HEqn]
          apply head.ifz₁_else
      have Hstep₂ : ((.ifz₁ (.binary₁ .sub (.lit n₂) (.lit n₂)) diverge (.lit 0)) ⭢* diverge) :=
        by
        -- head sub
        apply stepn.multi
        apply step_lvl.pure (fun X => .ifz₁ X diverge (.lit 0))
        . apply ctx𝕄.cons𝔹 _ _ (ctx𝔹.ifz₁ _ _ (typing.regular _ _ _ _ _ typing_diverge) (by simp)) ctx𝕄.hole
        . simp
        . apply head.binary₁
        -- head if else
        apply stepn.multi _ _ _ _ (stepn.refl _)
        apply step_lvl.pure _ _ _ ctx𝕄.hole
        . simp; apply typing.regular _ _ _ _ _ typing_diverge
        . simp; apply head.ifz₁_then
      have HE : ctx𝔼 (fun X => .ifz₁ (.binary₁ .sub X (.lit n₂)) diverge (.lit 0)) :=
        by
        apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.ifz₁ _ _ (typing.regular _ _ _ _ _ typing_diverge) (by simp))
        apply ctx𝔼.cons𝔹 _ _ (ctx𝔹.binaryl₁ _ _ (by simp))
        apply ctx𝔼.hole
      have HτE : ObsCtxℂ ⦰ .nat (fun X => .ifz₁ (.binary₁ .sub X (.lit n₂)) diverge (.lit 0)) ⦰ .nat :=
        by
        have HτC := ObsCtxℂ.hole ⦰ .nat
        have HτB := ObsCtx𝔽.ifz₁ _ _ _ _ typing_diverge (typing.lit _ _ 0)
        have HτC := ObsCtxℂ.cons𝔽 _ _ _ _ _ _ _ _ HτC HτB
        have HτB := ObsCtx𝔽.binaryl₁ ⦰ .sub _ (typing.lit _ _ n₂)
        apply ObsCtxℂ.cons𝔽 _ _ _ _ _ _ _ _ HτC HτB
      --
      --
      -- E⟦n₁⟧⇓
      -- ⦰ ⊧ n₁ ≤𝑐𝑖𝑢 n₂ : ℕ
      -- ——————————————————
      -- E⟦n₂⟧⇓
      have Htermination := Hciu_value _ typing.subst.nil _ _ HE HτE (by exists .lit 0)
      --
      --
      -- E⟦n₂⟧⇓
      -- E⟦n₂⟧ ⭢* diverge
      -- ——————————————————
      -- diverge⇓
      rw [← termination.under_stepn]
      apply Htermination
      apply Hstep₂
  case arrow τ𝕒 τ𝕓 ε IH𝕒 IH𝕓 =>
    have ⟨Hτ₁, Hτ₂, Hciu_value⟩ := Hciu
    cases ε <;> try simp at Hsem_value
    cases Hvalue₀ <;> try simp at Hsem_value
    case lam e₀ _ =>
    cases Hvalue₁ <;> try contradiction
    case lam e₁ _ =>
    cases Hvalue₂ <;> try contradiction
    case lam e₂ _ =>
    simp only [log_approx_value]
    constructor; simp only [log_approx_value] at Hsem_value; apply Hsem_value.left
    constructor; apply Hτ₂
    intros j Hindexj argv₀ argv₁ Hsem_value_arg
    have ⟨HvalueArg₀, HvalueArg₁⟩ := log_approx_value.syntactic.value _ _ _ _ Hsem_value_arg
    have ⟨HτArg₀, HτArg₁⟩ := log_approx_value.syntactic.typing _ _ _ _ Hsem_value_arg
    simp only [log_approx_expr]
    intros i Hindexi v₀ Hvalue₀ Hstep₀
    --
    --
    -- (k, λx.e₀, λx.e₁) ∈ 𝓥⟦τ𝕒 → τ𝕓⟧
    -- (j, argv₀, argv₁) ∈ 𝓥⟦τ𝕒⟧
    -- —————————————————————————————————————————
    -- (j, λx.e₀ @ argv₀, λx.e₁ @ argv₁) ∈ 𝓔⟦τ𝕓⟧
    have Hsem_expr := log_approx_value.apply j _ _ _ _ _ _ (log_approx_value.antimono _ _ _ _ _ Hsem_value (by omega)) Hsem_value_arg
    simp only [log_approx_expr] at Hsem_expr
    --
    --
    -- λx.e₀ @ argv₀ ⭢ ⟦i⟧ v₀
    -- (j, λx.e₀ @ argv₀, λx.e₁ @ argv₁) ∈ 𝓔⟦τ𝕓⟧
    -- —————————————————————————————————————————
    -- λx.e₁ @ argv₁ ⭢* v₁
    -- (j - i, v₀, v₁) ∈ 𝓥⟦τ𝕓⟧
    have ⟨v₁, Hstep₁, Hsem_value⟩ := Hsem_expr i Hindexi v₀ Hvalue₀ Hstep₀
    have ⟨Hvalue₀, Hvalue₁⟩ := log_approx_value.syntactic.value _ _ _ _ Hsem_value
    have ⟨Hτv₀, Hτv₁⟩ := log_approx_value.syntactic.typing _ _ _ _ Hsem_value
    --
    --
    -- ⦰ ⊢ (fun X => X @ argv₁)⟦⦰ ⊢ τ𝕒 → τ𝕓⟧ : τ𝕓
    -- ⦰ ⊧ λx.e₁ ≤𝑐𝑖𝑢 λx.e₂ : τ𝕒 → τ𝕓
    -- λx.e₁ @ argv₁ ⭢* v₁
    -- ———————————————————————————————————
    -- λx.e₂ @ argv₁ ⭢* v₂
    have HE : ctx𝔼 (fun X => .app₁ X argv₁) := ctx𝔼.cons𝔹 _ _ (ctx𝔹.appl₁ _ (lc.value _ HvalueArg₁)) ctx𝔼.hole
    have HτE : ObsCtxℂ ⦰ (τ𝕒.arrow τ𝕓 ⊥) (fun X => .app₁ X argv₁) ⦰ τ𝕓 := ObsCtxℂ.cons𝔽 _ _ _ _ _ _ _ _ (ObsCtxℂ.hole _ _) (ObsCtx𝔽.appl₁ _ _ _ _ HτArg₁)
    have ⟨v₂, Hvalue₂, Hstep₂⟩ := Hciu_value _ typing.subst.nil _ _ HE HτE (by exists v₁)
    --
    --
    -- ⦰ ⊢ λx.e₂ : τ𝕒 → τ𝕓
    -- ⦰ ⊢ argv₁ : τ𝕒
    -- λx.e₂ @ argv₁ ⭢* v₂
    -- ————————————————————
    -- ⦰ ⊢ v₂ : τ𝕓
    have Hτv₂ : typing ⦰ 𝟚 v₂ τ𝕓 ⊥ :=
      by
      apply preservation.dynamic _ _ _ Hstep₂
      rw [← Effect.union_pure ⊥, ← Effect.union_pure (⊥ ∪ ⊥)]
      apply typing.app₁; apply Hτ₂; apply HτArg₁
    exists v₂; constructor
    . apply Hstep₂
    . apply IH𝕓 _ _ _ _ Hvalue₀ Hvalue₁ Hvalue₂ Hsem_value
      constructor; apply Hτv₁
      constructor; apply Hτv₂
      intros γ Hγ E τ𝕖 HE HτE Htermination₁
      cases γ <;> cases Hγ
      --
      --
      -- λx.e₁ @ argv₁ ⭢* v₁
      -- E⟦v₁⟧⇓
      -- ————————————————————
      -- E⟦λx.e₁ @ argv₁⟧⇓
      have Htermination₁ : termination E⟦.app₁ (.lam e₁) argv₁⟧ :=
        by
        rw [termination.under_stepn]
        apply Htermination₁
        apply stepn_grounded.congruence_under_ctx𝔼 _ _ _ HE (
          by
          constructor
          . apply typing.dynamic_impl_grounded _ _ _ _ Hτ₁
          . apply typing.dynamic_impl_grounded _ _ _ _ HτArg₁
        ) Hstep₁
      --
      --
      -- ⦰ ⊢ E⟦⦰ ⊢ τ𝕓⟧ : τ𝕖
      -- ———————————————————————————————————————————————
      -- ⦰ ⊢ (E ∘ fun X => X @ argv₁)⟦⦰ ⊢ τ𝕒 → τ𝕓⟧ : τ𝕖
      have HEApp : ctx𝔼 (E ∘ fun X => .app₁ X argv₁) := compose.ctx𝔼_ctx𝔹 _ _ HE (ctx𝔹.appl₁ _ (lc.value _ HvalueArg₁))
      have HτEApp : ObsCtxℂ ⦰ (τ𝕒.arrow τ𝕓 ⊥) (E ∘ fun X => .app₁ X argv₁) ⦰ τ𝕖 := ObsCtxℂ.cons𝔽 _ _ _ _ _ _ _ _ HτE (ObsCtx𝔽.appl₁ _ _ _ _ HτArg₁)
      --
      --
      -- ⦰ ⊢ (E ∘ fun X => X @ argv₁)⟦⦰ ⊢ τ𝕒 → τ𝕓⟧ : τ𝕖
      -- ⦰ ⊧ λx.e₁ ≤𝑐𝑖𝑢 λx.e₂ : τ𝕒 → τ𝕓
      -- E⟦λx.e₁ @ argv₁⟧⇓
      -- ———————————————————————————————————————————————
      -- E⟦λx.e₂ @ argv₁⟧⇓
      have Htermination₂ := Hciu_value _ typing.subst.nil _ _ HEApp HτEApp Htermination₁
      --
      --
      -- E⟦λx.e₂ @ argv₁⟧⇓
      -- λx.e₂ @ argv₁ ⭢* v₂
      -- ———————————————————
      -- E⟦v₂⟧⇓
      rw [← termination.under_stepn]
      apply Htermination₂; apply stepn_grounded.congruence_under_ctx𝔼 _ _ _ HE (
        by
        constructor
        . apply typing.dynamic_impl_grounded _ _ _ _ Hτ₂
        . apply typing.dynamic_impl_grounded _ _ _ _ HτArg₁
      ) Hstep₂
  case fragment => simp at Hsem_value
  case rep => simp at Hsem_value

-- Γ ⊧ e₀ ≤𝑐𝑖𝑢 e₁ : τ
-- ——————————————————
-- Γ ⊧ e₀ ≤𝑙𝑜𝑔 e₁ : τ
theorem ciu_approx_impl_log_approx :
  ∀ Γ τ e₀ e₁,
    ciu_approx Γ e₀ e₁ τ →
    log_approx Γ e₀ e₁ τ :=
  by
  intros Γ τ e₀ e₁ Hciu
  have ⟨Hτ₀, Hτ₁, Hciu⟩ := Hciu
  constructor; apply Hτ₀
  constructor; apply Hτ₁
  intros k γ₀ γ₁ HsemΓ
  have ⟨Hγ₀, Hγ₁⟩ := log_approx_env.syntactic.typing _ _ _ _ HsemΓ
  have ⟨HSγ₀τ₀, HSγ₁τ₀⟩ := log_approx_env.msubst.typing _ _ _ _ _ _ _ Hτ₀ Hτ₀ HsemΓ
  have ⟨HSγ₀τ₁, HSγ₁τ₁⟩ := log_approx_env.msubst.typing _ _ _ _ _ _ _ Hτ₁ Hτ₁ HsemΓ
  simp only [log_approx_expr]
  intros j Hj v₀ Hvalue₀ Hstep₀
  --
  --
  -- γ₀(e₀) ⭢ ⟦j⟧ v₀
  -- Γ ⊢ e₀ : τ
  -- ——————————————————————
  -- γ₁(e₀) ⭢* v₁
  -- (k - j, v₀, v₁) ∈ 𝓥⟦τ⟧
  have ⟨_, _, Hsem_expr⟩ := log_approx.fundamental _ _ _ Hτ₀
  simp only [log_approx_expr] at Hsem_expr
  have ⟨v₁, Hstep₁, Hsem_value⟩ := Hsem_expr _ _ _ HsemΓ _ Hj _ Hvalue₀ Hstep₀
  have ⟨Hvalue₀, Hvalue₁⟩ := log_approx_value.syntactic.value _ _ _ _ Hsem_value
  have ⟨Hτv₀, Hτv₁⟩ := log_approx_value.syntactic.typing _ _ _ _ Hsem_value
  --
  --
  -- γ₁(e₀) ⭢* v₁
  -- Γ ⊧ e₀ ≤𝑐𝑖𝑢 e₁ : τ
  -- ——————————————————
  -- γ₁(e₁) ⭢* v₂
  have ⟨v₂, Hvalue₂, Hstep₂⟩ := Hciu _ Hγ₁ _ _ ctx𝔼.hole (ObsCtxℂ.hole _ _) (by exists v₁)
  --
  --
  -- γ₁(e₁) ⭢* v₂
  -- ⦰ ⊢ γ₁(e₁) : τ
  -- ———————————————
  -- ⦰ ⊢ v₂ : τ
  have Hτv₂ : typing ⦰ 𝟚 v₂ τ ⊥ := preservation.dynamic _ _ _ Hstep₂ HSγ₁τ₁
  exists v₂; constructor
  . apply Hstep₂
  . apply ciu_approx_respects_log_approx_value _ _ _ _ _ Hvalue₀ Hvalue₁ Hvalue₂ Hsem_value
    constructor; apply Hτv₁
    constructor; apply Hτv₂
    intros γ Hγ E τ𝕖 HE HτE Htermination₁
    cases γ <;> cases Hγ
    --
    --
    -- γ₁(e₀) ⭢* v₁
    -- E⟦v₁⟧⇓
    -- —————————————
    -- E⟦γ₁(e₀)⟧⇓
    have Htermination₁ : termination E⟦msubst γ₁ e₀⟧ :=
      by
      rw [termination.under_stepn]
      apply Htermination₁
      apply stepn_grounded.congruence_under_ctx𝔼 _ _ _ HE (typing.dynamic_impl_grounded _ _ _ _ HSγ₁τ₀) Hstep₁
    --
    --
    -- E⟦γ₁(e₀)⟧⇓
    -- Γ ⊧ e₀ ≤𝑐𝑖𝑢 e₁ : τ
    -- ——————————————————
    -- E⟦γ₁(e₁)⟧⇓
    have Htermination₂ := Hciu _ Hγ₁ _ _ HE HτE Htermination₁
    --
    --
    -- E⟦γ₁(e₁)⟧⇓
    -- γ₁(e₁) ⭢* v₂
    -- —————————————
    -- E⟦v₂⟧⇓
    rw [← termination.under_stepn]
    apply Htermination₂
    apply stepn_grounded.congruence_under_ctx𝔼 _ _ _ HE (typing.dynamic_impl_grounded _ _ _ _ HSγ₁τ₁) Hstep₂

-- Γ ⊧ e₀ ≤𝑐𝑡𝑥 e₁ : τ
-- ——————————————————
-- Γ ⊧ e₀ ≤𝑙𝑜𝑔 e₁ : τ
theorem log_approx.completeness :
  ∀ Γ τ e₀ e₁,
    ctx_approx Γ e₀ e₁ τ →
    log_approx Γ e₀ e₁ τ :=
  by
  intros Γ τ e₀ e₁ Hctx
  apply ciu_approx_impl_log_approx
  apply ctx_approx_impl_ciu_approx
  apply Hctx
