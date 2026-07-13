import Instar.TwoLevelRec.LogicalEquiv.LogicalRelation

-- Γ ⊧ x ≤𝑙𝑜𝑔 x : Γ(x)
lemma compatibility.fvar :
  ∀ Γ x τ,
    binds x (τ, 𝟚) Γ →
    wbt 𝟚 τ →
    log_approx Γ (.fvar x) (.fvar x) τ :=
  by
  intros Γ x τ Hbinds Hwbt
  constructor; apply typing.fvar; apply Hbinds; apply Hwbt
  constructor; apply typing.fvar; apply Hbinds; apply Hwbt
  intros k γ₀ γ₁ HsemΓ
  simp only [log_approx_expr]
  intros z Hindexz v₀ Hvalue₀ Hstep₀
  exists msubst γ₁ (.fvar x)
  constructor
  . apply stepn.refl
  . have Hsem_value := log_approx_env.binds_log_approx_value _ _ _ _ _ _ HsemΓ Hbinds
    have ⟨Hvalue₀, Hvalue₁⟩ := log_approx_value.syntactic.value _ _ _ _ Hsem_value
    have ⟨HEqv, Hz⟩ := stepn_indexed.value_impl_termination _ _ _ Hvalue₀ Hstep₀
    rw [← HEqv, Hz]; apply Hsem_value

-- Γ ⊧ n ≤𝑙𝑜𝑔 n : ℕ
lemma compatibility.lit :
  ∀ Γ n,
    log_approx Γ (.lit n) (.lit n) .nat :=
  by
  intros _ n
  constructor; apply typing.lit
  constructor; apply typing.lit
  intros k γ₀ γ₁ semΓ
  simp only [log_approx_expr]
  intros z Hindexz v₀ Hvalue₀ Hstep₀
  exists .lit n
  constructor
  . simp; apply stepn.refl
  . simp at Hstep₀
    have ⟨HEqv, Hz⟩ := stepn_indexed.value_impl_termination _ _ _ (value.lit n) Hstep₀
    simp [← HEqv, Hz]

-- x ↦ τ𝕒, Γ ⊧ e₀ ≤𝑙𝑜𝑔 e₁ : τ𝕓
-- ——————————————————————————————
-- Γ ⊧ λx.e₀ ≤𝑙𝑜𝑔 λx.e₁ : τ𝕒 → τ𝕓
lemma compatibility.lam :
  ∀ Γ e₀ e₁ τ𝕒 τ𝕓,
    wbt 𝟚 τ𝕒 →
    closed_at e₀ Γ.length →
    closed_at e₁ Γ.length →
    log_approx ((τ𝕒, 𝟚) :: Γ) ({0 ↦ Γ.length} e₀) ({0 ↦ Γ.length} e₁) τ𝕓 →
    log_approx Γ (.lam e₀) (.lam e₁) (.arrow τ𝕒 τ𝕓 ⊥) :=
  by
  intros Γ e₀ e₁ τ𝕒 τ𝕓 Hwbt Hclosed₀ Hclosed₁ He
  have ⟨Hτ₀, Hτ₁, He⟩ := He
  have Hτ₀ : typing Γ 𝟚 (.lam e₀) (.arrow τ𝕒 τ𝕓 ⊥) ⊥ := by apply typing.lam; apply Hτ₀; apply Hwbt; apply Hclosed₀
  have Hτ₁ : typing Γ 𝟚 (.lam e₁) (.arrow τ𝕒 τ𝕓 ⊥) ⊥ := by apply typing.lam; apply Hτ₁; apply Hwbt; apply Hclosed₁
  constructor; apply Hτ₀
  constructor; apply Hτ₁
  intros k γ₀ γ₁ HsemΓ
  have ⟨HSτ₀, HSτ₁⟩ := log_approx_env.msubst.typing _ _ _ _ _ _ _ Hτ₀ Hτ₁ HsemΓ
  have ⟨Hlc₀, Hclosed₀⟩ := typing.wf _ _ _ _ _ HSτ₀
  have ⟨Hlc₁, Hclosed₁⟩ := typing.wf _ _ _ _ _ HSτ₁
  simp at HSτ₀ HSτ₁ Hlc₀ Hlc₁ Hclosed₀ Hclosed₁
  have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.mwf _ _ _ _ HsemΓ
  have ⟨HEq₀, HEq₁⟩ := log_approx_env.length _ _ _ _ HsemΓ
  rw [log_approx_expr]
  intros z Hindexz v₀ Hvalue₀ Hstep₀
  --
  --
  -- λx.γ₀(e₀) ⭢ ⟦z⟧ v₀
  -- ——————————————————
  -- z = 0
  -- v₀ = λx.γ₀(e₀)
  simp at Hstep₀
  have ⟨HEqv₀, HEqz⟩ := stepn_indexed.value_impl_termination _ _ _ (value.lam _ Hlc₀) Hstep₀
  exists msubst γ₁ (.lam e₁)
  constructor; apply stepn.refl
  simp only [← HEqv₀, HEqz, msubst.lam, log_approx_value]
  constructor; apply HSτ₀
  constructor; apply HSτ₁
  intros k Hindexk argv₀ argv₁ Hsem_value_arg
  have ⟨HvalueArg₀, HvalueArg₁⟩ := log_approx_value.syntactic.value _ _ _ _ Hsem_value_arg
  have ⟨HτArg₀, HτArg₁⟩ := log_approx_value.syntactic.typing _ _ _ _ Hsem_value_arg
  have ⟨HlcArg₀, HclosedArg₀⟩ := typing.wf _ _ _ _ _ HτArg₀
  have ⟨HlcArg₁, HclosedArg₁⟩ := typing.wf _ _ _ _ _ HτArg₁
  rw [log_approx_expr]
  intros j Hindexj v₀ Hvalue₀ Hstep₀
  --
  --
  -- λx.γ₀(e₀) @ argv₀ ⭢ ⟦j⟧ v₀
  -- —————————————————————————————
  -- j = i + 1
  -- (x ↦ argv₀, γ₀)(e₀) ⭢ ⟦i⟧ v₀
  have ⟨i, HEqj, Hstep₀⟩ := stepn_indexed.refine.app₁.eliminator _ _ _ _ (value.lam _ Hlc₀) HvalueArg₀ Hvalue₀ Hstep₀
  --
  --
  -- (x ↦ argv₀, γ₀)(e₀) ⭢ ⟦i⟧ v₀
  -- (k, (x ↦ argv₀, γ₀)(e₀), (x ↦ argv₁, γ₁)(e₁)) ∈ 𝓔⟦τ𝕓⟧
  -- ——————————————————————————————————————————————————————
  -- (x ↦ argv₁, γ₁)(e₁) ⭢* v₁
  -- (k - i, v₀, v₁) ∈ 𝓥⟦τ𝕓⟧
  have HEqSubst₀ : opening 0 argv₀ (msubst γ₀ e₀) = msubst (argv₀ :: γ₀) ({0 ↦ Γ.length} e₀) :=
    by
    rw [msubst, ← comm.msubst_subst _ _ _ _ _ _ Hmwf₀]
    rw [comm.msubst_opening _ _ _ _ _ Hmwf₀]
    rw [HEq₀, intro.subst]
    apply closed.inc; apply Hclosed₀; simp
    omega; omega; apply HclosedArg₀
  rw [HEqSubst₀] at Hstep₀
  have HsemΓ : log_approx_env k (argv₀ :: γ₀) (argv₁ :: γ₁) ((τ𝕒, 𝟚) :: Γ) :=
    by
    apply log_approx_env.cons; apply Hsem_value_arg
    apply log_approx_env.antimono; apply HsemΓ; omega
  simp only [log_approx_expr] at He
  have ⟨v₁, Hstep₁, Hsem_value⟩ := He _ _ _ HsemΓ i (by omega) _ Hvalue₀ Hstep₀
  --
  --
  -- (x ↦ argv₁, γ₁)(e₁) ⭢* v₁
  -- ——————————————————————————
  -- λx.γ₁(e₁) @ argv₁ ⭢* v₁
  exists v₁
  constructor
  . have HEqSubst₁ : opening 0 argv₁ (msubst γ₁ e₁) = msubst (argv₁ :: γ₁) ({0 ↦ Γ.length} e₁) :=
      by
      rw [msubst, ← comm.msubst_subst _ _ _ _ _ _ Hmwf₁]
      rw [comm.msubst_opening _ _ _ _ _ Hmwf₁]
      rw [HEq₁, intro.subst]
      apply closed.inc; apply Hclosed₁; omega
      omega; omega; apply HclosedArg₁
    rw [← HEqSubst₁] at Hstep₁
    apply stepn.multi _ _ _ _ Hstep₁
    apply step_lvl.pure _ _ _ ctx𝕄.hole
    constructor; apply Hlc₁; apply lc.value; apply HvalueArg₁
    apply head.app₁; apply HvalueArg₁
  . apply log_approx_value.antimono
    apply Hsem_value; omega

-- Γ ⊧ f₀ ≤𝑙𝑜𝑔 f₁ : τ𝕒 → τ𝕓
-- Γ ⊧ arg₀ ≤𝑙𝑜𝑔 arg₁ : τ𝕒
-- —————————————————————————————————
-- Γ ⊧ f₀ @ arg₀ ≤𝑙𝑜𝑔 f₁ @ arg₁ : τ𝕓
lemma compatibility.app₁ :
  ∀ Γ f₀ f₁ arg₀ arg₁ τ𝕒 τ𝕓,
    log_approx Γ f₀ f₁ (.arrow τ𝕒 τ𝕓 ⊥) →
    log_approx Γ arg₀ arg₁ τ𝕒 →
    log_approx Γ (.app₁ f₀ arg₀) (.app₁ f₁ arg₁) τ𝕓 :=
  by
  intros Γ f₀ f₁ arg₀ arg₁ τ𝕒 τ𝕓 Hf Harg
  have ⟨HτFun₀, HτFun₁, Hf⟩ := Hf
  have ⟨HτArg₀, HτArg₁, Harg⟩ := Harg
  have Hτ₀ : typing Γ 𝟚 (.app₁ f₀ arg₀) τ𝕓 ⊥ :=
    by
    rw [← Effect.union_pure ⊥, ← Effect.union_pure (⊥ ∪ ⊥)]
    apply typing.app₁; apply HτFun₀; apply HτArg₀
  have Hτ₁ : typing Γ 𝟚 (.app₁ f₁ arg₁) τ𝕓 ⊥ :=
    by
    rw [← Effect.union_pure ⊥, ← Effect.union_pure (⊥ ∪ ⊥)]
    apply typing.app₁; apply HτFun₁; apply HτArg₁
  constructor; apply Hτ₀
  constructor; apply Hτ₁
  intros k γ₀ γ₁ HsemΓ
  have ⟨HSτFun₀, HSτFun₁⟩ := log_approx_env.msubst.typing _ _ _ _ _ _ _ HτFun₀ HτFun₁ HsemΓ
  have ⟨HSτArg₀, HSτArg₁⟩ := log_approx_env.msubst.typing _ _ _ _ _ _ _ HτArg₀ HτArg₁ HsemΓ
  have ⟨HSτ₀, HSτ₁⟩ := log_approx_env.msubst.typing _ _ _ _ _ _ _ Hτ₀ Hτ₁ HsemΓ
  simp at HSτ₀ HSτ₁
  have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.mwf _ _ _ _ HsemΓ
  simp only [log_approx_expr]
  intros j Hindexj v₀ Hvalue₀ Hstep₀
  --
  --
  -- γ₀(f₀) @ γ₀(arg₀) ⭢ ⟦j⟧ v₀
  -- ———————————————————————————
  -- i₀ + i₁ + i₂ = j
  -- γ₀(f₀) ⭢ ⟦i₀⟧ fv₀
  -- γ₀(arg₀) ⭢ ⟦i₁⟧ argv₀
  -- fv₀ @ argv₀ ⭢ ⟦i₂⟧ v₀
  simp at Hstep₀
  have ⟨i₀, i₁, i₂, fv₀, argv₀, HEqj, HvalueFun₀, HvalueArg₀, HstepFun₀, HstepArg₀, Hstep₀⟩ :=
    stepn_indexed.refine.app₁.constructor _ _ _ _ Hvalue₀ (typing.dynamic_impl_grounded _ _ _ _ HSτ₀) Hstep₀
  --
  --
  -- γ₀(f₀) ⭢ ⟦i₀⟧ fv₀
  -- Γ ⊧ f₀ ≤𝑙𝑜𝑔 f₁ : τ𝕒 → τ𝕓
  -- ———————————————————————————————
  -- γ₁(f₁) ⭢* fv₁
  -- (k - i₀, fv₀, fv₁) ∈ 𝓥⟦τ𝕒 → τ𝕓⟧
  simp only [log_approx_expr] at Hf
  have ⟨fv₁, HstepFun₁, Hsem_value_fun⟩ := Hf _ _ _ HsemΓ i₀ (by omega) _ HvalueFun₀ HstepFun₀
  have ⟨HvalueFun₀, HvalueFun₁⟩ := log_approx_value.syntactic.value _ _ _ _ Hsem_value_fun
  --
  --
  -- γ₀(arg₀) ⭢ ⟦i₁⟧ argv₀
  -- Γ ⊧ arg₀ ≤𝑙𝑜𝑔 arg₁ : τ𝕒
  -- ——————————————————————————————
  -- γ₁(arg₁) ⭢* argv₁
  -- (k - i₁, argv₀, argv₁) ∈ 𝓥⟦τ𝕒⟧
  simp only [log_approx_expr] at Harg
  have ⟨argv₁, HstepArg₁, Hsem_value_arg⟩ := Harg _ _ _ HsemΓ i₁ (by omega) _ HvalueArg₀ HstepArg₀
  --
  --
  -- (k - i₀, fv₀, fv₁) ∈ 𝓥⟦τ𝕒 → τ𝕓⟧
  -- (k - i₁, argv₀, argv₁) ∈ 𝓥⟦τ𝕒⟧
  -- ———————————————————————————————————————————————
  -- (k - i₀ - i₁, fv₀ @ argv₀, fv₁ @ argv₁) ∈ 𝓔⟦τ𝕓⟧
  have Hsem_value_fun : log_approx_value (k - i₀ - i₁) fv₀ fv₁ (τ𝕒.arrow τ𝕓 ⊥) := log_approx_value.antimono _ _ _ _ _ Hsem_value_fun (by omega)
  have Hsem_value_arg : log_approx_value (k - i₀ - i₁) argv₀ argv₁ τ𝕒 := log_approx_value.antimono _ _ _ _ _ Hsem_value_arg (by omega)
  have Hsem_expr := log_approx_value.apply _ _ _ _ _ _ _ Hsem_value_fun Hsem_value_arg
  --
  --
  -- (k - i₀ - i₁, fv₀ @ argv₀, fv₁ @ argv₁) ∈ 𝓔⟦τ𝕓⟧
  -- fv₀ @ argv₀ ⭢ ⟦i₂⟧ v₀
  -- ———————————————————————————————————————————————
  -- fv₁ @ argv₁ ⭢* v₁
  -- (k - i₀ - i₁ - i₂, v₀, v₁) ∈ 𝓥⟦τ𝕓⟧
  simp only [log_approx_expr] at Hsem_expr
  have ⟨v₁, Hstep₁, Hsem_value⟩ := Hsem_expr i₂ (by omega) v₀ Hvalue₀ Hstep₀
  --
  --
  -- γ₁(f₁) ⭢* fv₁
  -- γ₁(arg₁) ⭢* argv₁
  -- fv₁ @ argv₁ ⭢* v₁
  -- ————————————————————————
  -- γ₁(f₁) @ γ₁(arg₁) ⭢* v₁
  exists v₁; constructor
  . simp
    -- left
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.appl₁ _ _)
    apply typing.dynamic_impl_grounded _ _ _ _ HSτFun₁; apply HstepFun₁
    apply typing.regular _ _ _ _ _ HSτArg₁
    -- right
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.appr₁ _ HvalueFun₁)
    apply typing.dynamic_impl_grounded _ _ _ _ HSτArg₁; apply HstepArg₁
    -- head
    apply Hstep₁
  . apply log_approx_value.antimono
    apply Hsem_value; omega

-- Γ ⊧ l₀ ≤𝑙𝑜𝑔 l₁ : ℕ
-- Γ ⊧ r₀ ≤𝑙𝑜𝑔 r₁ : ℕ
-- ——————————————————————————————
-- Γ ⊧ l₀ ⊕ r₀ ≤𝑙𝑜𝑔 l₁ ⊕ r₁ : ℕ
lemma compatibility.binary₁ :
  ∀ Γ op l₀ l₁ r₀ r₁,
    log_approx Γ l₀ l₁ .nat →
    log_approx Γ r₀ r₁ .nat →
    log_approx Γ (.binary₁ op l₀ r₀) (.binary₁ op l₁ r₁) .nat :=
  by
  intros Γ op l₀ l₁ r₀ r₁ Hl Hr
  have ⟨Hτl₀, Hτl₁, Hl⟩ := Hl
  have ⟨Hτr₀, Hτr₁, Hr⟩ := Hr
  have Hτ₀ : typing Γ 𝟚 (.binary₁ op l₀ r₀) .nat ⊥ :=
    by
    rw [← Effect.union_pure ⊥, ← Effect.union_pure (⊥ ∪ ⊥)]
    apply typing.binary₁; apply Hτl₀; apply Hτr₀
  have Hτ₁ : typing Γ 𝟚 (.binary₁ op l₁ r₁) .nat ⊥ :=
    by
    rw [← Effect.union_pure ⊥, ← Effect.union_pure (⊥ ∪ ⊥)]
    apply typing.binary₁; apply Hτl₁; apply Hτr₁
  constructor; apply Hτ₀
  constructor; apply Hτ₁
  intros k γ₀ γ₁ HsemΓ
  have ⟨HSτl₀, HSτl₁⟩ := log_approx_env.msubst.typing _ _ _ _ _ _ _ Hτl₀ Hτl₁ HsemΓ
  have ⟨HSτr₀, HSτr₁⟩ := log_approx_env.msubst.typing _ _ _ _ _ _ _ Hτr₀ Hτr₁ HsemΓ
  have ⟨HSτ₀, HSτ₁⟩ := log_approx_env.msubst.typing _ _ _ _ _ _ _ Hτ₀ Hτ₁ HsemΓ
  simp at HSτ₀ HSτ₁
  have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.mwf _ _ _ _ HsemΓ
  rw [log_approx_expr]
  intros j Hindex v₀ Hvalue₀ Hstep₀
  --
  --
  -- γ₀(l₀) ⊕ γ₀(r₀) ⭢ ⟦j⟧ v₀
  -- —————————————————————————
  -- i₀ + i₁ + i₂ = j
  -- γ₀(l₀) ⭢ ⟦i₀⟧ lv₀
  -- γ₀(r₀) ⭢ ⟦i₁⟧ rv₀
  -- lv₀ ⊕ rv₀ ⭢ ⟦i₂⟧ v₀
  simp at Hstep₀
  have ⟨i₀, i₁, i₂, lv₀, rv₀, HEqj, Hvaluel₀, Hvaluer₀, Hstepl₀, Hstepr₀, Hstep₀⟩ :=
    stepn_indexed.refine.binary₁.constructor _ _ _ _ _ Hvalue₀ (typing.dynamic_impl_grounded _ _ _ _ HSτ₀) Hstep₀
  --
  --
  -- γ₀(l₀) ⭢ ⟦i₀⟧ lv₀
  -- Γ ⊧ l₀ ≤𝑙𝑜𝑔 l₁ : ℕ
  -- ——————————————————
  -- γ₁(l₁) ⭢* lv₁
  -- lv₀ = lv₁
  simp only [log_approx_expr] at Hl
  have ⟨lv₁, Hstepl₁, Hsem_valuel⟩ := Hl _ _ _ HsemΓ i₀ (by omega) _ Hvaluel₀ Hstepl₀
  have ⟨Hvaluel₀, Hvaluel₁⟩ := log_approx_value.syntactic.value _ _ _ _ Hsem_valuel
  cases Hvaluel₀ <;> try simp at Hsem_valuel
  case lit lv₀ =>
  cases Hvaluel₁ <;> try simp at Hsem_valuel
  case lit lv₁ =>
  --
  --
  -- γ₀(r₀) ⭢ ⟦i₁⟧ rv₀
  -- Γ ⊧ r₀ ≤𝑙𝑜𝑔 r₁ : ℕ
  -- ——————————————————
  -- γ₁(r₁) ⭢* rv₁
  -- rv₀ = rv₁
  simp only [log_approx_expr] at Hr
  have ⟨rv₁, Hstepr₁, Hsem_valuer⟩ := Hr _ _ _ HsemΓ i₁ (by omega) _ Hvaluer₀ Hstepr₀
  have ⟨Hvaluer₀, Hvaluer₁⟩ := log_approx_value.syntactic.value _ _ _ _ Hsem_valuer
  cases Hvaluer₀ <;> try simp at Hsem_valuer
  case lit rv₀ =>
  cases Hvaluer₁ <;> try simp at Hsem_valuer
  case lit rv₁ =>
  --
  --
  -- lv₀ ⊕ rv₀ ⭢ ⟦i₂⟧ v₀
  -- ————————————————————
  -- v₀ = lv₀ ⊕ rv₀
  have ⟨_, HEqv₀⟩ := stepn_indexed.refine.binary₁.eliminator _ _ _ _ _ Hvalue₀ Hstep₀
  --
  --
  -- γ₁(l₁) ⭢* lv₁
  -- γ₁(r₁) ⭢* rv₁
  -- ——————————————————————————————
  -- γ₁(l₁) ⊕ γ₁(r₁) ⭢* lv₁ ⊕ rv₁
  exists v₀; constructor
  . simp
    -- left
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.binaryl₁ _ _ _)
    apply typing.dynamic_impl_grounded _ _ _ _ HSτl₁; apply Hstepl₁
    apply lc.under_msubst; apply Hmwf₁
    apply typing.regular _ _ _ _ _ Hτr₁
    -- right
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.binaryr₁ _ _ (value.lit _))
    apply typing.dynamic_impl_grounded _ _ _ _ HSτr₁; apply Hstepr₁
    -- head
    rw [← Hsem_valuel, ← Hsem_valuer]
    apply stepn_indexed_impl_stepn _ _ _ Hstep₀
  . simp [HEqv₀]

-- Γ ⊧ b₀ ≤𝑙𝑜𝑔 b₁ : τ𝕒
-- x ↦ τ𝕒, Γ ⊧ e₀ ≤𝑙𝑜𝑔 e₁ : τ𝕓
-- —————————————————————————————————————————————————
-- Γ ⊧ lets x = b₀ in e₀ ≤𝑙𝑜𝑔 lets x = b₁ in e₁ : τ𝕓
lemma compatibility.lets :
  ∀ Γ b₀ b₁ e₀ e₁ τ𝕒 τ𝕓,
    wbt 𝟚 τ𝕒 →
    closed_at e₀ Γ.length →
    closed_at e₁ Γ.length →
    log_approx Γ b₀ b₁ τ𝕒 →
    log_approx ((τ𝕒, 𝟚) :: Γ) ({0 ↦ Γ.length} e₀) ({0 ↦ Γ.length} e₁) τ𝕓 →
    log_approx Γ (.lets b₀ e₀) (.lets b₁ e₁) τ𝕓 :=
  by
  intros Γ b₀ b₁ e₀ e₁ τ𝕒 τ𝕓 Hwbt Hclosed₀ Hclosed₁ Hb He
  have ⟨Hτb₀, Hτb₁, Hb⟩ := Hb
  have ⟨Hτe₀, Hτe₁, He⟩ := He
  have Hτ₀ : typing Γ 𝟚 (.lets b₀ e₀) τ𝕓 ⊥ :=
    by
    rw [← Effect.union_pure ⊥]; apply typing.lets
    apply Hτb₀; apply Hτe₀; apply Hwbt; apply Hclosed₀
  have Hτ₁ : typing Γ 𝟚 (.lets b₁ e₁) τ𝕓 ⊥ :=
    by
    rw [← Effect.union_pure ⊥]; apply typing.lets
    apply Hτb₁; apply Hτe₁; apply Hwbt; apply Hclosed₁
  constructor; apply Hτ₀
  constructor; apply Hτ₁
  intros k γ₀ γ₁ HsemΓ
  have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.mwf _ _ _ _ HsemΓ
  have ⟨HEq₀, HEq₁⟩ := log_approx_env.length _ _ _ _ HsemΓ
  have ⟨HSτ₀, HSτ₁⟩ := log_approx_env.msubst.typing _ _ _ _ _ _ _ Hτ₀ Hτ₁ HsemΓ
  have ⟨HSτb₀, HSτb₁⟩ := log_approx_env.msubst.typing _ _ _ _ _ _ _ Hτb₀ Hτb₁ HsemΓ
  have ⟨Hlc₀, Hclosed₀⟩ := typing.wf _ _ _ _ _ HSτ₀
  have ⟨Hlc₁, Hclosed₁⟩ := typing.wf _ _ _ _ _ HSτ₁
  simp at HSτ₀ HSτ₁ Hlc₀ Hlc₁ Hclosed₀ Hclosed₁
  rw [log_approx_expr]
  intros j Hindexj v₀ Hvalue₀ Hstep₀
  --
  --
  -- lets x = γ₀(b₀) in γ₀(e₀) ⭢ ⟦j⟧ v₀
  -- ——————————————————————————————————
  -- i₀ + 1 + i₁ = j
  -- γ₀(b₀) ⭢ ⟦i₀⟧ bv₀
  -- (x ↦ bv₀, γ₀)(e₀) ⭢ ⟦i₁⟧ v₀
  simp at Hstep₀
  have ⟨i₀, i₁, bv₀, HEqj, HvalueBind₀, HstepBind₀, Hstep₀⟩ :=
    stepn_indexed.refine.lets _ _ _ _ Hvalue₀ (typing.dynamic_impl_grounded _ _ _ _ HSτ₀) Hstep₀
  --
  --
  -- γ₀(b₀) ⭢ ⟦i₀⟧ bv₀
  -- Γ ⊧ b₀ ≤𝑙𝑜𝑔 b₁ : τ𝕒
  -- ——————————————————————————
  -- γ₁(b₁) ⭢* bv₁
  -- (k - i₀, bv₀, bv₁) ∈ 𝓥⟦τ𝕒⟧
  simp only [log_approx_expr] at Hb
  have ⟨bv₁, HstepBind₁, Hsem_value_bind⟩ := Hb _ _ _ HsemΓ i₀ (by omega) _ HvalueBind₀ HstepBind₀
  have ⟨HvalueBind₀, HvalueBind₁⟩ := log_approx_value.syntactic.value _ _ _ _ Hsem_value_bind
  have ⟨HτBind₀, HτBind₁⟩ := log_approx_value.syntactic.typing _ _ _ _ Hsem_value_bind
  have ⟨HlcBind₀, HclosedBind₀⟩ := typing.wf _ _ _ _ _ HτBind₀
  have ⟨HlcBind₁, HclosedBind₁⟩ := typing.wf _ _ _ _ _ HτBind₁
  --
  --
  -- (x ↦ bv₀, γ₀)(e₀) ⭢ ⟦i₁⟧ v₀
  -- (k - i₀, (x ↦ bv₀, γ₀)(e₀), (x ↦ bv₁, γ₁)(e₁)) ∈ 𝓔⟦τ𝕓⟧
  -- ———————————————————————————————————————————————————————
  -- (x ↦ bv₁, γ₁)(e₁) ⭢* v₁
  -- (k - i₀ - i₁, v₀, v₁) ∈ 𝓥⟦τ𝕓⟧
  have HEqSubst₀ : opening 0 bv₀ (msubst γ₀ e₀) = msubst (bv₀ :: γ₀) ({0 ↦ Γ.length} e₀) :=
    by
    rw [msubst, ← comm.msubst_subst _ _ _ _ _ _ Hmwf₀]
    rw [comm.msubst_opening _ _ _ _ _ Hmwf₀]
    rw [HEq₀, intro.subst]
    apply closed.inc; apply Hclosed₀.right; omega
    omega; omega; apply HclosedBind₀
  rw [HEqSubst₀] at Hstep₀
  have HsemΓ : log_approx_env (k - i₀) (bv₀ :: γ₀) (bv₁ :: γ₁) ((τ𝕒, 𝟚) :: Γ) :=
    by
    apply log_approx_env.cons; apply Hsem_value_bind
    apply log_approx_env.antimono; apply HsemΓ; omega
  have Hsem_expr := He _ _ _ HsemΓ
  rw [log_approx_expr] at Hsem_expr
  have ⟨v₁, Hstep₁, Hsem_value⟩ := Hsem_expr i₁ (by omega) _ Hvalue₀ Hstep₀
  --
  --
  -- γ₁(b₁) ⭢* bv₁
  -- (x ↦ bv₁, γ₁)(e₁) ⭢* v₁
  -- ———————————————————————————————
  -- lets x = γ₁(b₁) in γ₁(e₁) ⭢* v₁
  exists v₁
  constructor
  . simp
    -- left
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.lets _ Hlc₁.right) (typing.dynamic_impl_grounded _ _ _ _ HSτb₁) HstepBind₁
    -- head
    have HEqSubst₁ : opening 0 bv₁ (msubst γ₁ e₁) = msubst (bv₁ :: γ₁) ({0 ↦ Γ.length} e₁) :=
      by
      rw [msubst, ← comm.msubst_subst _ _ _ _ _ _ Hmwf₁]
      rw [comm.msubst_opening _ _ _ _ _ Hmwf₁]
      rw [HEq₁, intro.subst]
      apply closed.inc; apply Hclosed₁.right; omega
      omega; omega; apply HclosedBind₁
    rw [← HEqSubst₁] at Hstep₁
    apply stepn.multi _ _ _ _ Hstep₁
    apply step_lvl.pure _ _ _ ctx𝕄.hole
    constructor; apply HlcBind₁; apply Hlc₁.right
    apply head.lets; apply HvalueBind₁
  . apply log_approx_value.antimono
    apply Hsem_value; omega

lemma compatibility.fix₁.induction :
  ∀ k f₀ f₁ τ𝕒 τ𝕓,
    log_approx_value k f₀ f₁ (.arrow (.arrow τ𝕒 τ𝕓 ⊥) (.arrow τ𝕒 τ𝕓 ⊥) ⊥) →
    log_approx_value k
      (.lam (.app₁ (.app₁ f₀ (.fix₁ f₀)) (.bvar 0)))
      (.lam (.app₁ (.app₁ f₁ (.fix₁ f₁)) (.bvar 0)))
    (.arrow τ𝕒 τ𝕓 ⊥) :=
  by
  intros k f₀ f₁ τ𝕒 τ𝕓 Hsem_value_fix
  have ⟨HvalueFix₀, HvalueFix₁⟩ := log_approx_value.syntactic.value _ _ _ _ Hsem_value_fix
  have ⟨HτFix₀, HτFix₁⟩ := log_approx_value.syntactic.typing _ _ _ _ Hsem_value_fix
  have ⟨HlcFix₀, HclosedFix₀⟩ := typing.wf _ _ _ _ _ HτFix₀
  have ⟨HlcFix₁, HclosedFix₁⟩ := typing.wf _ _ _ _ _ HτFix₁
  have Hwbt: wbt 𝟚 τ𝕒 := by cases HvalueFix₀ <;> cases HτFix₀; next Hwbt _ => apply Hwbt.right.left
  have Hτ₀ : typing ⦰ 𝟚 (.lam (.app₁ (.app₁ f₀ (.fix₁ f₀)) (.bvar 0))) (.arrow τ𝕒 τ𝕓 ⊥) ⊥ :=
    by
    apply typing.lam; rw [← Effect.union_pure ⊥, ← Effect.union_pure (⊥ ∪ ⊥)]
    apply typing.app₁; rw [← Effect.union_pure ⊥, ← Effect.union_pure (⊥ ∪ ⊥), identity.opening _ _ _ (by simp; apply HlcFix₀)]
    apply typing.weakening.singleton
    apply typing.app₁; apply HτFix₀
    apply typing.fix₁; simp; rfl; apply HτFix₀
    apply typing.fvar; simp; apply Hwbt; apply Hwbt
    simp; apply HclosedFix₀
  have Hτ₁ : typing ⦰ 𝟚 (.lam (.app₁ (.app₁ f₁ (.fix₁ f₁)) (.bvar 0))) (.arrow τ𝕒 τ𝕓 ⊥) ⊥ :=
    by
    apply typing.lam; rw [← Effect.union_pure ⊥, ← Effect.union_pure (⊥ ∪ ⊥)]
    apply typing.app₁; rw [← Effect.union_pure ⊥, ← Effect.union_pure (⊥ ∪ ⊥), identity.opening _ _ _ (by simp; apply HlcFix₁)]
    apply typing.weakening.singleton
    apply typing.app₁; apply HτFix₁
    apply typing.fix₁; simp; rfl; apply HτFix₁
    apply typing.fvar; simp; apply Hwbt; apply Hwbt
    simp; apply HclosedFix₁
  induction k
  case zero =>
    rw [log_approx_value]
    constructor; apply Hτ₀
    constructor; apply Hτ₁
    intro z Hindexz argv₀ argv₁ Hsem_value_arg
    rw [log_approx_expr]
    intro j Hindexj; omega
  case succ k IH =>
    rw [log_approx_value]
    constructor; apply Hτ₀
    constructor; apply Hτ₁
    intros s Hindexs argv₀ argv₁ Hsem_value_arg
    have ⟨HvalueArg₀, HvalueArg₁⟩ := log_approx_value.syntactic.value _ _ _ _ Hsem_value_arg
    have ⟨HτArg₀, HτArg₁⟩ := log_approx_value.syntactic.typing _ _ _ _ Hsem_value_arg
    have ⟨HlcArg₀, HclosedArg₀⟩ := typing.wf _ _ _ _ _ HτArg₀
    have ⟨HlcArg₁, HclosedArg₁⟩ := typing.wf _ _ _ _ _ HτArg₁
    rw [log_approx_expr]
    intro j Hindexj v₀ Hvalue₀ Hstep₀
    --
    --
    -- (λx.f₀ @ fix f₀ @ x) @ argv₀ ⭢ ⟦j⟧ v₀
    -- ——————————————————————————————————————————
    -- i + 2 = j
    -- f₀ @ (λx.f₀ @ fix f₀ @ x) @ argv₀ ⭢ ⟦i⟧ v₀
    have ⟨i, HEqj, Hstep₀⟩ :=
      stepn_indexed.refine.fix₁.eliminator _ _ _ _ HvalueFix₀ HvalueArg₀ Hvalue₀ (
        by simp; apply typing.dynamic_impl_grounded _ _ _ _ HτFix₀
      ) Hstep₀
    --
    --
    -- f₀ @ (λx.f₀ @ fix f₀ @ x) @ argv₀ ⭢ ⟦i⟧ v₀
    -- ——————————————————————————————————————————
    -- i₀ + i₁ = i
    -- f₀ @ (λx.f₀ @ fix f₀ @ x) ⭢ ⟦i₀⟧ fv₀
    -- fv₀ @ argv₀ ⭢ ⟦i₁⟧ v₀
    have ⟨i₀, z, i₁, fv₀, _, HEqj, HvalueFun₀, _, HstepFun₀, HstepArg₀, Hstep₀⟩ :=
      stepn_indexed.refine.app₁.constructor _ _ _ _ Hvalue₀ (
          by
          simp; constructor
          apply typing.dynamic_impl_grounded _ _ _ _ HτFix₀
          apply typing.dynamic_impl_grounded _ _ _ _ HτArg₀
      ) Hstep₀
    have ⟨HEqv, Hz⟩ := stepn_indexed.value_impl_termination _ _ _ HvalueArg₀ HstepArg₀
    rw [← HEqv] at Hstep₀
    --
    --
    -- (k + 1, f₀, f₁) ∈ 𝓥⟦(τ𝕒 → τ𝕓) → (τ𝕒 → τ𝕓)⟧
    -- (k, λx.f₀ @ fix f₀ @ x, λx.f₁ @ fix f₁ @ x) ∈ 𝓥⟦τ𝕒 → τ𝕓⟧
    -- —————————————————————————————————————————————————————————————————————
    -- (k, f₀ @ (λx.f₀ @ fix f₀ @ x), f₁ @ (λx.f₁ @ fix f₁ @ x)) ∈ 𝓔⟦τ𝕒 → τ𝕓⟧
    have Hsem_expr_fun :
      log_approx_expr k
        (.app₁ f₀ (.lam (.app₁ (.app₁ f₀ (.fix₁ f₀)) (.bvar 0))))
        (.app₁ f₁ (.lam (.app₁ (.app₁ f₁ (.fix₁ f₁)) (.bvar 0))))
      (.arrow τ𝕒 τ𝕓 ⊥) :=
      by
      apply log_approx_value.apply
      apply log_approx_value.antimono; apply Hsem_value_fix; omega
      apply IH; apply log_approx_value.antimono; apply Hsem_value_fix; omega
    --
    --
    -- f₀ @ (λx.f₀ @ fix f₀ @ x) ⭢ ⟦i₀⟧ fv₀
    -- (k, f₀ @ (λx.f₀ @ fix f₀ @ x), f₁ @ (λx.f₁ @ fix f₁ @ x)) ∈ 𝓔⟦τ𝕒 → τ𝕓⟧
    -- —————————————————————————————————————————————————————————————————————
    -- f₁ @ (λx.f₁ @ fix f₁ @ x) ⭢* fv₁
    -- (k - i₀, fv₀, fv₁) ∈ 𝓥⟦τ𝕒 → τ𝕓⟧
    rw [log_approx_expr] at Hsem_expr_fun
    have ⟨fv₁, HstepFun₁, Hsem_value_fun⟩ := Hsem_expr_fun i₀ (by omega) _ HvalueFun₀ HstepFun₀
    --
    --
    -- (k - i₀, fv₀, fv₁) ∈ 𝓥⟦τ𝕒 → τ𝕓⟧
    -- (s, argv₀, argv₁) ∈ 𝓥⟦τ𝕒⟧
    -- —————————————————————————————————————————————
    -- (s - i₀ - 1, fv₀ @ argv₀, fv₁ @ argv₁) ∈ 𝓔⟦τ𝕓⟧
    have Hsem_value_fun : log_approx_value (s - i₀ - 1) fv₀ fv₁ (τ𝕒.arrow τ𝕓 ⊥) := log_approx_value.antimono _ _ _ _ _ Hsem_value_fun (by omega)
    have Hsem_value_arg : log_approx_value (s - i₀ - 1) argv₀ argv₁ τ𝕒 := log_approx_value.antimono _ _ _ _ _ Hsem_value_arg (by omega)
    have Hsem_expr := log_approx_value.apply _ _ _ _ _ _ _ Hsem_value_fun Hsem_value_arg
    --
    --
    -- (s - i₀ - 1, fv₀ @ argv₀, fv₁ @ argv₁) ∈ 𝓔⟦τ𝕓⟧
    -- fv₀ @ argv₀ ⭢ ⟦i₁⟧ v₀
    -- —————————————————————————————————————————————
    -- fv₁ @ argv₁ ⭢* v₁
    -- (s - i₀ - i₁ - 1, v₀, v₁) ∈ 𝓥⟦τ𝕓⟧
    simp only [log_approx_expr] at Hsem_expr
    have ⟨v₁, Hstep₁, Hsem_value⟩ := Hsem_expr i₁ (by omega) v₀ Hvalue₀ Hstep₀
    --
    --
    -- f₁ @ (λx.f₁ @ fix f₁ @ x) ⭢* fv₁
    -- fv₁ @ argv₁ ⭢* v₁
    -- ——————————————————————————————————
    -- (λx.f₁ @ fix f₁ @ x) @ argv₁ ⭢* v₁
    exists v₁
    constructor
    . -- head₀
      apply stepn.multi
      apply step_lvl.pure _ _ _ ctx𝕄.hole
      simp; constructor
      apply lc.inc; apply HlcFix₁; omega
      apply HlcArg₁
      apply head.app₁; apply HvalueArg₁
      simp [identity.opening _ _ _ HlcFix₁]
      -- head₁
      apply stepn.multi
      apply step_grounded.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.appl₁ _ (lc.value _ HvalueArg₁))
      simp; apply typing.dynamic_impl_grounded _ _ _ _ HτFix₁
      apply step_grounded.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.appr₁ _ HvalueFix₁)
      simp; apply typing.dynamic_impl_grounded _ _ _ _ HτFix₁
      apply step_lvl.pure _ _ _ ctx𝕄.hole
      apply HlcFix₁
      apply head.fix₁; apply HvalueFix₁
      -- left
      apply stepn.trans
      apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.appl₁ _ _)
      simp; apply typing.dynamic_impl_grounded _ _ _ _ HτFix₁; apply HstepFun₁
      apply HlcArg₁
      -- head₂
      apply Hstep₁
    . apply log_approx_value.antimono
      apply Hsem_value; omega

-- Γ ⊧ f₀ ≤𝑙𝑜𝑔 f₁ : (τ𝕒 → τ𝕓) → (τ𝕒 → τ𝕓)
-- ——————————————————————————————————————
-- Γ ⊧ fix f₀ ≤𝑙𝑜𝑔 fix f₁ : τ𝕒 → τ𝕓
lemma compatibility.fix₁ :
  ∀ Γ f₀ f₁ τ𝕒 τ𝕓,
    log_approx Γ f₀ f₁ (.arrow (.arrow τ𝕒 τ𝕓 ⊥) (.arrow τ𝕒 τ𝕓 ⊥) ⊥) →
    log_approx Γ (.fix₁ f₀) (.fix₁ f₁) (.arrow τ𝕒 τ𝕓 ⊥) :=
  by
  intros Γ f₀ f₁ τ𝕒 τ𝕓 Hf
  have ⟨HτFix₀, HτFix₁, Hf⟩ := Hf
  have Hτ₀ : typing Γ 𝟚 (.fix₁ f₀) (.arrow τ𝕒 τ𝕓 ⊥) ⊥ := by apply typing.fix₁; simp; rfl; apply HτFix₀
  have Hτ₁ : typing Γ 𝟚 (.fix₁ f₁) (.arrow τ𝕒 τ𝕓 ⊥) ⊥ := by apply typing.fix₁; simp; rfl; apply HτFix₁
  constructor; apply Hτ₀
  constructor; apply Hτ₁
  intros k γ₀ γ₁ HsemΓ
  have ⟨HSτFix₀, HSτFix₁⟩ := log_approx_env.msubst.typing _ _ _ _ _ _ _ HτFix₀ HτFix₁ HsemΓ
  simp only [msubst.fix₁, log_approx_expr]
  intros j Hindexj v₀ Hvalue₀ Hstep₀
  --
  --
  -- fix γ₀(f₀) ⭢ ⟦j⟧ v₀
  -- ——————————————————————————
  -- i₀ + 1 = j
  -- γ₀(f₀) ⭢ ⟦i₀⟧ fv₀
  -- v₀ = λx.fv₀ @ fix fv₀ @ x
  have ⟨i₀, fv₀, HEqj, HvalueFix₀, HstepFix₀, HEqv₀⟩ :=
    stepn_indexed.refine.fix₁.constructor _ _ _ Hvalue₀ (
      by
      simp; apply typing.dynamic_impl_grounded _ _ _ _ HSτFix₀
    ) Hstep₀
  rw [HEqv₀]
  --
  --
  -- γ₀(f₀) ⭢ ⟦i₀⟧ fv₀
  -- (k, γ₀(f₀), γ₁(f₁)) ∈ 𝓔⟦(τ𝕒 → τ𝕓) → (τ𝕒 → τ𝕓)⟧
  -- ———————————————————————————————————————————————
  -- γ₁(f₁) ⭢* fv₁
  -- (k - i₀, fv₀, fv₁) ∈ 𝓥⟦(τ𝕒 → τ𝕓) → (τ𝕒 → τ𝕓)⟧
  simp only [log_approx_expr] at Hf
  have ⟨fv₁, HstepFix₁, Hsem_value_fix⟩ := Hf _ _ _ HsemΓ i₀ (by omega) _ HvalueFix₀ HstepFix₀
  have ⟨HvalueFix₀, HvalueFix₁⟩ := log_approx_value.syntactic.value _ _ _ _ Hsem_value_fix
  --
  --
  -- γ₁(f₁) ⭢* fv₁
  -- ———————————————————————————————————
  -- fix γ₁(f₁) ⭢* λx.fv₁ @ fix fv₁ @ x
  exists .lam (.app₁ (.app₁ fv₁ (.fix₁ fv₁)) (.bvar 0))
  constructor
  . -- left
    apply stepn.trans
    apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ ctx𝔹.fix₁
    apply typing.dynamic_impl_grounded _ _ _ _ HSτFix₁; apply HstepFix₁
    -- head
    apply stepn.multi _ _ _ _ (stepn.refl _)
    apply step_lvl.pure _ _ _ ctx𝕄.hole
    simp; apply lc.value; apply HvalueFix₁
    apply head.fix₁; apply HvalueFix₁
  . apply compatibility.fix₁.induction
    apply log_approx_value.antimono
    apply Hsem_value_fix; omega

-- Γ ⊧ c₀ ≤𝑙𝑜𝑔 c₁ : ℕ
-- Γ ⊧ l₀ ≤𝑙𝑜𝑔 l₁ : τ
-- Γ ⊧ r₀ ≤𝑙𝑜𝑔 r₁ : τ
-- ————————————————————————————————————————————————————————
-- Γ ⊧ if c₀ then l₀ else r₀ ≤𝑙𝑜𝑔 if c₁ then l₁ else r₁ : τ
lemma compatibility.ifz₁ :
  ∀ Γ c₀ c₁ l₀ l₁ r₀ r₁ τ,
    log_approx Γ c₀ c₁ .nat →
    log_approx Γ l₀ l₁ τ →
    log_approx Γ r₀ r₁ τ →
    log_approx Γ (.ifz₁ c₀ l₀ r₀) (.ifz₁ c₁ l₁ r₁) τ :=
  by
  intros Γ c₀ c₁ l₀ l₁ r₀ r₁ τ Hc Hl Hr
  have ⟨Hτc₀, Hτc₁, Hc⟩ := Hc
  have ⟨Hτl₀, Hτl₁, Hl⟩ := Hl
  have ⟨Hτr₀, Hτr₁, Hr⟩ := Hr
  have Hτ₀ : typing Γ 𝟚 (.ifz₁ c₀ l₀ r₀) τ ⊥ :=
    by
    rw [← Effect.union_pure ⊥, ← Effect.union_pure (⊥ ∪ ⊥)]
    apply typing.ifz₁; apply Hτc₀; apply Hτl₀; apply Hτr₀
  have Hτ₁ : typing Γ 𝟚 (.ifz₁ c₁ l₁ r₁) τ ⊥ :=
    by
    rw [← Effect.union_pure ⊥, ← Effect.union_pure (⊥ ∪ ⊥)]
    apply typing.ifz₁; apply Hτc₁; apply Hτl₁; apply Hτr₁
  constructor; apply Hτ₀
  constructor; apply Hτ₁
  intros k γ₀ γ₁ HsemΓ
  have ⟨HSτc₀, HSτc₁⟩ := log_approx_env.msubst.typing _ _ _ _ _ _ _ Hτc₀ Hτc₁ HsemΓ
  have ⟨HSτl₀, HSτl₁⟩ := log_approx_env.msubst.typing _ _ _ _ _ _ _ Hτl₀ Hτl₁ HsemΓ
  have ⟨HSτr₀, HSτr₁⟩ := log_approx_env.msubst.typing _ _ _ _ _ _ _ Hτr₀ Hτr₁ HsemΓ
  have ⟨HSτ₀, HSτ₁⟩ := log_approx_env.msubst.typing _ _ _ _ _ _ _ Hτ₀ Hτ₁ HsemΓ
  simp at HSτ₀ HSτ₁
  have ⟨Hmwf₀, Hmwf₁⟩ := log_approx_env.mwf _ _ _ _ HsemΓ
  rw [log_approx_expr]
  intros j Hindex v₀ Hvalue₀ Hstep₀
  --
  --
  -- if γ₀(c₀) then γ₀(l₀) else γ₀(r₀) ⭢ ⟦j⟧ v₀
  -- ——————————————————————————————————————————
  -- i₀ + i₁ = j
  -- γ₀(c₀) ⭢ ⟦i₀⟧ cv₀
  -- if cv₀ then γ₀(l₀) else γ₀(r₀) ⭢ ⟦i₁⟧ v₀
  simp at Hstep₀
  have ⟨i₀, i₁, cv₀, HEqj, Hvaluec₀, Hstepc₀, Hstep₀⟩ :=
    stepn_indexed.refine.ifz₁.constructor _ _ _ _ _ Hvalue₀ (typing.dynamic_impl_grounded _ _ _ _ HSτ₀) Hstep₀
  --
  --
  -- γ₀(c₀) ⭢ ⟦i₀⟧ cv₀
  -- Γ ⊧ c₀ ≤𝑙𝑜𝑔 c₁ : ℕ
  -- ——————————————————
  -- γ₁(c₁) ⭢* cv₁
  -- cv₀ = cv₁
  simp only [log_approx_expr] at Hc
  have ⟨cv₁, Hstepc₁, Hsem_valuec⟩ := Hc _ _ _ HsemΓ i₀ (by omega) _ Hvaluec₀ Hstepc₀
  have ⟨Hvaluec₀, Hvaluec₁⟩ := log_approx_value.syntactic.value _ _ _ _ Hsem_valuec
  cases Hvaluec₀ <;> try simp at Hsem_valuec
  case lit cv₀ =>
  cases Hvaluec₁ <;> try simp at Hsem_valuec
  case lit cv₁ =>
  match cv₀, cv₁ with
  | .succ _, .zero => nomatch Hsem_valuec
  | .zero, .succ _ => nomatch Hsem_valuec
  --
  --
  -- then branch
  | .zero, .zero =>
    --
    --
    -- if 0 then γ₀(l₀) else γ₀(r₀) ⭢ ⟦i₁⟧ v₀
    -- ———————————————————————————————————————
    -- i₂ + 1 = i₁
    -- γ₀(l₀) ⭢ ⟦i₂⟧ v₀
    have ⟨i₂, HEqi₁, Hstep₀⟩ := stepn_indexed.refine.ifz₁_then.eliminator _ _ _ _ Hvalue₀ Hstep₀
    --
    --
    -- γ₀(l₀) ⭢ ⟦i₂⟧ v₀
    -- Γ ⊧ l₀ ≤𝑙𝑜𝑔 l₁ : τ
    -- ——————————————————————
    -- γ₁(l₁) ⭢* v₁
    -- (k - i₂, v₀, v₁) ∈ 𝓥⟦τ⟧
    simp only [log_approx_expr] at Hl
    have ⟨v₁, Hstep₁, Hsem_value⟩ := Hl _ _ _ HsemΓ i₂ (by omega) _ Hvalue₀ Hstep₀
    --
    --
    -- γ₁(c₁) ⭢* 0
    -- γ₁(l₁) ⭢* v₁
    -- ————————————————————————————————————————
    -- if γ₁(c₁) then γ₁(l₁) else γ₁(r₁) ⭢* v₁
    exists v₁; constructor
    . -- condition
      simp
      apply stepn.trans
      apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.ifz₁ _ _ _ _)
      apply typing.dynamic_impl_grounded _ _ _ _ HSτc₁; apply Hstepc₁
      apply typing.regular _ _ _ _ _ HSτl₁; apply typing.regular _ _ _ _ _ HSτr₁
      -- head
      apply stepn.multi _ _ _ _ Hstep₁
      apply step_lvl.pure _ _ _ ctx𝕄.hole
      simp; constructor; apply typing.regular _ _ _ _ _ HSτl₁; apply typing.regular _ _ _ _ _ HSτr₁
      apply head.ifz₁_then
    . apply log_approx_value.antimono
      apply Hsem_value; omega
  --
  --
  -- else branch
  | .succ cv₀, .succ cv₁ =>
    --
    --
    -- if (n + 1) then γ₀(l₀) else γ₀(r₀) ⭢ ⟦i₁⟧ v₀
    -- ————————————————————————————————————————————
    -- i₂ + 1 = i₁
    -- γ₀(r₀) ⭢ ⟦i₂⟧ v₀
    have ⟨i₂, HEqi₁, Hstep₀⟩ := stepn_indexed.refine.ifz₁_else.eliminator _ _ _ _ _ Hvalue₀ Hstep₀
    --
    --
    -- γ₀(r₀) ⭢ ⟦i₂⟧ v₀
    -- Γ ⊧ r₀ ≤𝑙𝑜𝑔 r₁ : τ
    -- ——————————————————————
    -- γ₁(r₁) ⭢* v₁
    -- (k - i₂, v₀, v₁) ∈ 𝓥⟦τ⟧
    simp only [log_approx_expr] at Hr
    have ⟨v₁, Hstep₁, Hsem_value⟩ := Hr _ _ _ HsemΓ i₂ (by omega) _ Hvalue₀ Hstep₀
    --
    --
    -- γ₁(c₁) ⭢* n + 1
    -- γ₁(r₁) ⭢* v₁
    -- ————————————————————————————————————————
    -- if γ₁(c₁) then γ₁(l₁) else γ₁(r₁) ⭢* v₁
    exists v₁; constructor
    . simp
      -- condition
      apply stepn.trans
      apply stepn_grounded.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.ifz₁ _ _ _ _)
      apply typing.dynamic_impl_grounded _ _ _ _ HSτc₁; apply Hstepc₁
      apply typing.regular _ _ _ _ _ HSτl₁; apply typing.regular _ _ _ _ _ HSτr₁
      -- head
      apply stepn.multi _ _ _ _ Hstep₁
      apply step_lvl.pure _ _ _ ctx𝕄.hole
      simp; constructor; apply typing.regular _ _ _ _ _ HSτl₁; apply typing.regular _ _ _ _ _ HSτr₁
      apply head.ifz₁_else
    . apply log_approx_value.antimono
      apply Hsem_value; omega
