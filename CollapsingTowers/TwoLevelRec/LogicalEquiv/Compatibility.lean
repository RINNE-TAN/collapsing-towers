import CollapsingTowers.TwoLevelRec.LogicalEquiv.LogicalRelation

-- Γ ⊧ x ≤𝑙𝑜𝑔 x : Γ(x)
lemma compatibility.fvar :
  ∀ Γ x τ,
    binds x (τ, 𝟚) Γ →
    wbt 𝟚 τ →
    log_rel_typing Γ (.fvar x) (.fvar x) τ :=
  by
  intros Γ x τ Hbinds Hwbt
  constructor; apply typing.fvar; apply Hbinds; apply Hwbt
  constructor; apply typing.fvar; apply Hbinds; apply Hwbt
  intros k γ₀ γ₁ HsemΓ
  simp only [log_rel_expr]
  intros z Hindexz v₀ Hvalue₀ Hstep₀
  exists multi_subst γ₁ (.fvar x)
  constructor
  . apply stepn.refl
  . have Hsem_value := log_rel_env.binds_log_rel_value _ _ _ _ _ _ HsemΓ Hbinds
    have ⟨Hvalue₀, Hvalue₁⟩ := log_rel_value.syntactic.value _ _ _ _ Hsem_value
    have ⟨HEqv, Hz⟩ := stepn_indexed.value_impl_termination _ _ _ Hvalue₀ Hstep₀
    rw [← HEqv, Hz]; apply Hsem_value

-- Γ ⊧ n ≤𝑙𝑜𝑔 n : ℕ
lemma compatibility.lit :
  ∀ Γ n, log_rel_typing Γ (.lit n) (.lit n) .nat :=
  by
  intros _ n
  constructor; apply typing.lit
  constructor; apply typing.lit
  intros k γ₀ γ₁ semΓ
  simp only [log_rel_expr]
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
    log_rel_typing ((τ𝕒, 𝟚) :: Γ) ({0 ↦ Γ.length} e₀) ({0 ↦ Γ.length} e₁) τ𝕓 →
    log_rel_typing Γ (.lam e₀) (.lam e₁) (.arrow τ𝕒 τ𝕓 ∅) :=
  by
  intros Γ e₀ e₁ τ𝕒 τ𝕓 Hwbt Hclosed₀ Hclosed₁ He
  have ⟨Hτ₀, Hτ₁, He⟩ := He
  have Hτ₀ : typing Γ 𝟚 (.lam e₀) (.arrow τ𝕒 τ𝕓 ∅) ∅ := by apply typing.lam; apply Hτ₀; apply Hwbt; apply Hclosed₀
  have Hτ₁ : typing Γ 𝟚 (.lam e₁) (.arrow τ𝕒 τ𝕓 ∅) ∅ := by apply typing.lam; apply Hτ₁; apply Hwbt; apply Hclosed₁
  constructor; apply Hτ₀
  constructor; apply Hτ₁
  intros k γ₀ γ₁ HsemΓ
  have ⟨HSτ₀, HSτ₁⟩ := log_rel_env.multi_subst.typing _ _ _ _ _ _ _ Hτ₀ Hτ₁ HsemΓ
  have ⟨Hlc₀, Hclosed₀⟩ := typing.wf _ _ _ _ _ HSτ₀
  have ⟨Hlc₁, Hclosed₁⟩ := typing.wf _ _ _ _ _ HSτ₁
  simp at HSτ₀ HSτ₁ Hlc₀ Hlc₁ Hclosed₀ Hclosed₁
  have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := log_rel_env.multi_wf _ _ _ _ HsemΓ
  have ⟨HEq₀, HEq₁⟩ := log_rel_env.length _ _ _ _ HsemΓ
  rw [log_rel_expr]
  intros z Hindexz v₀ Hvalue₀ Hstep₀
  --
  --
  -- λx.γ₀(e₀) ⇝ ⟦z⟧ v₀
  -- ——————————————————
  -- z = 0
  -- v₀ = λx.γ₀(e₀)
  simp at Hstep₀
  have ⟨HEqv₀, HEqz⟩ := stepn_indexed.value_impl_termination _ _ _ (value.lam _ Hlc₀) Hstep₀
  exists multi_subst γ₁ (.lam e₁)
  constructor; apply stepn.refl
  simp only [← HEqv₀, HEqz, multi_subst.lam, log_rel_value]
  constructor; apply HSτ₀
  constructor; apply HSτ₁
  intros k Hindexk argv₀ argv₁ Hsem_value_arg
  have ⟨HvalueArg₀, HvalueArg₁⟩ := log_rel_value.syntactic.value _ _ _ _ Hsem_value_arg
  have ⟨HτArg₀, HτArg₁⟩ := log_rel_value.syntactic.typing _ _ _ _ Hsem_value_arg
  have ⟨HlcArg₀, HclosedArg₀⟩ := typing.wf _ _ _ _ _ HτArg₀
  have ⟨HlcArg₁, HclosedArg₁⟩ := typing.wf _ _ _ _ _ HτArg₁
  rw [log_rel_expr]
  intros j Hindexj v₀ Hvalue₀ Hstep₀
  --
  --
  -- λx.γ₀(e₀) @ argv₀ ⇝ ⟦j⟧ v₀
  -- —————————————————————————————
  -- j = i + 1
  -- (x ↦ argv₀, γ₀)(e₀) ⇝ ⟦i⟧ v₀
  have ⟨i, HEqj, Hstep₀⟩ := stepn_indexed.refine.lam _ _ _ _ (value.lam _ Hlc₀) HvalueArg₀ Hvalue₀ Hstep₀
  --
  --
  -- (x ↦ argv₀, γ₀)(e₀) ⇝ ⟦i⟧ v₀
  -- ((x ↦ argv₀, γ₀)(e₀), (x ↦ argv₁, γ₁)(e₁)) ∈ 𝓔⟦τ𝕓⟧{k}
  -- ——————————————————————————————————————————————————————
  -- (x ↦ argv₁, γ₁)(e₁) ⇝* v₁
  -- (v₀, v₁) ∈ 𝓥⟦τ𝕓⟧{k - i}
  have HEqSubst₀ : opening 0 argv₀ (multi_subst γ₀ e₀) = multi_subst (argv₀ :: γ₀) ({0 ↦ Γ.length} e₀) :=
    by
    rw [multi_subst, ← comm.multi_subst_subst _ _ _ _ _ _ Hmulti_wf₀]
    rw [comm.multi_subst_opening _ _ _ _ _ Hmulti_wf₀]
    rw [HEq₀, intros.subst]
    apply closed.inc; apply Hclosed₀; simp
    omega; omega; apply HclosedArg₀
  rw [HEqSubst₀] at Hstep₀
  have HsemΓ : log_rel_env k (argv₀ :: γ₀) (argv₁ :: γ₁) ((τ𝕒, 𝟚) :: Γ) :=
    by
    apply log_rel_env.cons; apply Hsem_value_arg
    apply log_rel_env.antimono; apply HsemΓ; omega
  have Hsem_expr := He _ _ _ HsemΓ
  rw [log_rel_expr] at Hsem_expr
  have ⟨v₁, Hstep₁, Hsem_value⟩ := Hsem_expr i (by omega) _ Hvalue₀ Hstep₀
  --
  --
  -- (x ↦ argv₁, γ₁)(e₁) ⇝* v₁
  -- ——————————————————————————
  -- λx.γ₁(e₁) @ argv₁ ⇝* v₁
  exists v₁
  constructor
  . have HEqSubst₁ : opening 0 argv₁ (multi_subst γ₁ e₁) = multi_subst (argv₁ :: γ₁) ({0 ↦ Γ.length} e₁) :=
      by
      rw [multi_subst, ← comm.multi_subst_subst _ _ _ _ _ _ Hmulti_wf₁]
      rw [comm.multi_subst_opening _ _ _ _ _ Hmulti_wf₁]
      rw [HEq₁, intros.subst]
      apply closed.inc; apply Hclosed₁; omega
      omega; omega; apply HclosedArg₁
    rw [← HEqSubst₁] at Hstep₁
    apply stepn.multi _ _ _ _ Hstep₁
    apply step_lvl.pure id; apply ctx𝕄.hole
    constructor; apply Hlc₁; apply lc.value; apply HvalueArg₁
    apply head.app₁; apply HvalueArg₁
  . apply log_rel_value.antimono
    apply Hsem_value; omega

-- Γ ⊧ f₀ ≤𝑙𝑜𝑔 f₁ : τ𝕒 → τ𝕓
-- Γ ⊧ arg₀ ≤𝑙𝑜𝑔 arg₁ : τ𝕒
-- —————————————————————————————————
-- Γ ⊧ f₀ @ arg₀ ≤𝑙𝑜𝑔 f₁ @ arg₁ : τ𝕓
lemma compatibility.app₁ :
  ∀ Γ f₀ f₁ arg₀ arg₁ τ𝕒 τ𝕓,
    log_rel_typing Γ f₀ f₁ (.arrow τ𝕒 τ𝕓 ∅) →
    log_rel_typing Γ arg₀ arg₁ τ𝕒 →
    log_rel_typing Γ (.app₁ f₀ arg₀) (.app₁ f₁ arg₁) τ𝕓 :=
  by
  intros Γ f₀ f₁ arg₀ arg₁ τ𝕒 τ𝕓 Hf Harg
  have ⟨HτFun₀, HτFun₁, Hf⟩ := Hf
  have ⟨HτArg₀, HτArg₁, Harg⟩ := Harg
  have Hτ₀ : typing Γ 𝟚 (.app₁ f₀ arg₀) τ𝕓 ∅ :=
    by
    rw [← union_pure_left ∅, ← union_pure_left ∅]
    apply typing.app₁; apply HτFun₀; apply HτArg₀
  have Hτ₁ : typing Γ 𝟚 (.app₁ f₁ arg₁) τ𝕓 ∅ :=
    by
    rw [← union_pure_left ∅, ← union_pure_left ∅]
    apply typing.app₁; apply HτFun₁; apply HτArg₁
  constructor; apply Hτ₀
  constructor; apply Hτ₁
  intros k γ₀ γ₁ HsemΓ
  have ⟨HSτFun₀, HSτFun₁⟩ := log_rel_env.multi_subst.typing _ _ _ _ _ _ _ HτFun₀ HτFun₁ HsemΓ
  have ⟨HSτArg₀, HSτArg₁⟩ := log_rel_env.multi_subst.typing _ _ _ _ _ _ _ HτArg₀ HτArg₁ HsemΓ
  have ⟨HSτ₀, HSτ₁⟩ := log_rel_env.multi_subst.typing _ _ _ _ _ _ _ Hτ₀ Hτ₁ HsemΓ
  simp at HSτ₀ HSτ₁
  have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := log_rel_env.multi_wf _ _ _ _ HsemΓ
  rw [log_rel_expr]
  intros j Hindex v₀ Hvalue₀ Hstep₀
  --
  --
  -- γ₀(f₀) @ γ₀(arg₀) ⇝ ⟦j⟧ v₀
  -- ———————————————————————————
  -- i₀ + i₁ + i₂ = j
  -- γ₀(f₀) ⇝ ⟦i₀⟧ fv₀
  -- γ₀(arg₀) ⇝ ⟦i₁⟧ argv₀
  -- fv₀ @ argv₀ ⇝ ⟦i₂⟧ v₀
  simp at Hstep₀
  have ⟨i₀, i₁, i₂, fv₀, argv₀, HEqj, HvalueFun₀, HvalueArg₀, HstepFun₀, HstepArg₀, Hstep₀⟩ :=
    stepn_indexed.refine.app₁ _ _ _ _ Hvalue₀ (typing.grounded_at_dyn _ _ _ _ HSτ₀) Hstep₀
  --
  --
  -- γ₀(f₀) ⇝ ⟦i₀⟧ fv₀
  -- Γ ⊧ f₀ ≤𝑙𝑜𝑔 f₁ : τ𝕒 → τ𝕓
  -- ———————————————————————————————
  -- γ₁(f₁) ⇝* fv₁
  -- (fv₀, fv₁) ∈ 𝓥⟦τ𝕒 → τ𝕓⟧{k - i₀}
  simp only [log_rel_expr] at Hf
  have ⟨fv₁, HstepFun₁, Hsem_value_fun⟩ := Hf _ _ _ HsemΓ i₀ (by omega) _ HvalueFun₀ HstepFun₀
  have ⟨HvalueFun₀, HvalueFun₁⟩ := log_rel_value.syntactic.value _ _ _ _ Hsem_value_fun
  --
  --
  -- γ₀(arg₀) ⇝ ⟦i₁⟧ argv₀
  -- Γ ⊧ arg₀ ≤𝑙𝑜𝑔 arg₁ : τ𝕒
  -- ——————————————————————————————
  -- γ₁(arg₁) ⇝* argv₁
  -- (argv₀, argv₁) ∈ 𝓥⟦τ𝕒⟧{k - i₁}
  simp only [log_rel_expr] at Harg
  have ⟨argv₁, HstepArg₁, Hsem_value_arg⟩ := Harg _ _ _ HsemΓ i₁ (by omega) _ HvalueArg₀ HstepArg₀
  --
  --
  -- (fv₀, fv₁) ∈ 𝓥⟦τ𝕒 → τ𝕓⟧{k - i₀}
  -- (argv₀, argv₁) ∈ 𝓥⟦τ𝕒⟧{k - i₁}
  -- ———————————————————————————————————————————————
  -- (fv₀ @ argv₀, fv₁ @ argv₁) ∈ 𝓔⟦τ𝕓⟧{k - i₀ - i₁}
  have Hsem_value_fun : log_rel_value (k - i₀ - i₁) fv₀ fv₁ (τ𝕒.arrow τ𝕓 ∅) := log_rel_value.antimono _ _ _ _ _ Hsem_value_fun (by omega)
  have Hsem_value_arg : log_rel_value (k - i₀ - i₁) argv₀ argv₁ τ𝕒 := log_rel_value.antimono _ _ _ _ _ Hsem_value_arg (by omega)
  have Hsem_expr := log_rel_value.apply _ _ _ _ _ _ _ Hsem_value_fun Hsem_value_arg
  --
  --
  -- (fv₀ @ argv₀, fv₁ @ argv₁) ∈ 𝓔⟦τ𝕓⟧{k - i₀ - i₁}
  -- fv₀ @ argv₀ ⇝ ⟦i₂⟧ v₀
  -- ———————————————————————————————————————————————
  -- fv₁ @ argv₁ ⇝* v₁
  -- (v₀, v₁) ∈ 𝓥⟦τ𝕓⟧{k - i₀ - i₁ - i₂}
  simp only [log_rel_expr] at Hsem_expr
  have ⟨v₁, Hstep₁, Hsem_value⟩ := Hsem_expr i₂ (by omega) v₀ Hvalue₀ Hstep₀
  --
  --
  -- γ₁(f₁) ⇝* fv₁
  -- γ₁(arg₁) ⇝* argv₁
  -- fv₁ @ argv₁ ⇝* v₁
  -- ————————————————————————
  -- γ₁(f₁) @ γ₁(arg₁) ⇝* v₁
  exists v₁; constructor
  . simp
    -- left
    apply stepn.trans
    apply stepn.grounded.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.appl₁ _ _)
    apply typing.grounded_at_dyn; apply HSτFun₁; apply HstepFun₁
    apply lc.under_multi_subst; apply Hmulti_wf₁
    apply typing.regular; apply HτArg₁
    -- right
    apply stepn.trans
    apply stepn.grounded.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.appr₁ _ HvalueFun₁)
    apply typing.grounded_at_dyn; apply HSτArg₁; apply HstepArg₁
    -- head
    apply Hstep₁
  . apply log_rel_value.antimono
    apply Hsem_value; omega

-- Γ ⊧ b₀ ≤𝑙𝑜𝑔 b₁ : τ𝕒
-- x ↦ τ𝕒, Γ ⊧ e₀ ≤𝑙𝑜𝑔 e₁ : τ𝕓
-- —————————————————————————————————————————————————
-- Γ ⊧ lets x = b₀ in e₀ ≤𝑙𝑜𝑔 lets x = b₁ in e₁ : τ𝕓
lemma compatibility.lets :
  ∀ Γ b₀ b₁ e₀ e₁ τ𝕒 τ𝕓,
    wbt 𝟚 τ𝕒 →
    closed_at e₀ Γ.length →
    closed_at e₁ Γ.length →
    log_rel_typing Γ b₀ b₁ τ𝕒 →
    log_rel_typing ((τ𝕒, 𝟚) :: Γ) ({0 ↦ Γ.length} e₀) ({0 ↦ Γ.length} e₁) τ𝕓 →
    log_rel_typing Γ (.lets b₀ e₀) (.lets b₁ e₁) τ𝕓 :=
  by
  intros Γ b₀ b₁ e₀ e₁ τ𝕒 τ𝕓 Hwbt Hclosed₀ Hclosed₁ Hb He
  have ⟨Hτb₀, Hτb₁, Hb⟩ := Hb
  have ⟨Hτe₀, Hτe₁, He⟩ := He
  have Hτ₀ : typing Γ 𝟚 (.lets b₀ e₀) τ𝕓 ∅ :=
    by
    rw [← union_pure_left ∅]; apply typing.lets
    apply Hτb₀; apply Hτe₀; apply Hwbt; apply Hclosed₀
  have Hτ₁ : typing Γ 𝟚 (.lets b₁ e₁) τ𝕓 ∅ :=
    by
    rw [← union_pure_left ∅]; apply typing.lets
    apply Hτb₁; apply Hτe₁; apply Hwbt; apply Hclosed₁
  constructor; apply Hτ₀
  constructor; apply Hτ₁
  intros k γ₀ γ₁ HsemΓ
  have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := log_rel_env.multi_wf _ _ _ _ HsemΓ
  have ⟨HEq₀, HEq₁⟩ := log_rel_env.length _ _ _ _ HsemΓ
  have ⟨HSτ₀, HSτ₁⟩ := log_rel_env.multi_subst.typing _ _ _ _ _ _ _ Hτ₀ Hτ₁ HsemΓ
  have ⟨HSτb₀, HSτb₁⟩ := log_rel_env.multi_subst.typing _ _ _ _ _ _ _ Hτb₀ Hτb₁ HsemΓ
  have ⟨Hlc₀, Hclosed₀⟩ := typing.wf _ _ _ _ _ HSτ₀
  have ⟨Hlc₁, Hclosed₁⟩ := typing.wf _ _ _ _ _ HSτ₁
  simp at HSτ₀ HSτ₁ Hlc₀ Hlc₁ Hclosed₀ Hclosed₁
  rw [log_rel_expr]
  intros j Hindexj v₀ Hvalue₀ Hstep₀
  --
  --
  -- lets x = γ₀(b₀) in γ₀(e₀) ⇝ ⟦j⟧ v₀
  -- ——————————————————————————————————
  -- i₀ + 1 + i₁ = j
  -- γ₀(b₀) ⇝ ⟦i₀⟧ bv₀
  -- (x ↦ bv₀, γ₀)(e₀) ⇝ ⟦i₁⟧ v₀
  simp at Hstep₀
  have ⟨i₀, i₁, bv₀, HEqj, HvalueBind₀, HstepBind₀, Hstep₀⟩ :=
    stepn_indexed.refine.lets _ _ _ _ Hvalue₀ (typing.grounded_at_dyn _ _ _ _ HSτ₀) Hstep₀
  --
  --
  -- γ₀(b₀) ⇝ ⟦i₀⟧ bv₀
  -- Γ ⊧ b₀ ≤𝑙𝑜𝑔 b₁ : τ𝕒 → τ𝕓
  -- ———————————————————————————————
  -- γ₁(b₁) ⇝* bv₁
  -- (bv₀, bv₁) ∈ 𝓥⟦τ𝕒 → τ𝕓⟧{k - i₀}
  simp only [log_rel_expr] at Hb
  have ⟨bv₁, HstepBind₁, Hsem_value_bind⟩ := Hb _ _ _ HsemΓ i₀ (by omega) _ HvalueBind₀ HstepBind₀
  have ⟨HvalueBind₀, HvalueBind₁⟩ := log_rel_value.syntactic.value _ _ _ _ Hsem_value_bind
  have ⟨HτBind₀, HτBind₁⟩ := log_rel_value.syntactic.typing _ _ _ _ Hsem_value_bind
  have ⟨HlcBind₀, HclosedBind₀⟩ := typing.wf _ _ _ _ _ HτBind₀
  have ⟨HlcBind₁, HclosedBind₁⟩ := typing.wf _ _ _ _ _ HτBind₁
  --
  --
  -- (x ↦ bv₀, γ₀)(e₀) ⇝ ⟦i₁⟧ v₀
  -- ((x ↦ bv₀, γ₀)(e₀), (x ↦ bv₁, γ₁)(e₁)) ∈ 𝓔⟦τ𝕓⟧{k - i₀}
  -- ———————————————————————————————————————————————————————
  -- (x ↦ bv₁, γ₁)(e₁) ⇝* v₁
  -- (v₀, v₁) ∈ 𝓥⟦τ𝕓⟧{k - i₀ - i₁}
  have HEqSubst₀ : opening 0 bv₀ (multi_subst γ₀ e₀) = multi_subst (bv₀ :: γ₀) ({0 ↦ Γ.length} e₀) :=
    by
    rw [multi_subst, ← comm.multi_subst_subst _ _ _ _ _ _ Hmulti_wf₀]
    rw [comm.multi_subst_opening _ _ _ _ _ Hmulti_wf₀]
    rw [HEq₀, intros.subst]
    apply closed.inc; apply Hclosed₀.right; omega
    omega; omega; apply HclosedBind₀
  rw [HEqSubst₀] at Hstep₀
  have HsemΓ : log_rel_env (k - i₀) (bv₀ :: γ₀) (bv₁ :: γ₁) ((τ𝕒, 𝟚) :: Γ) :=
    by
    apply log_rel_env.cons; apply Hsem_value_bind
    apply log_rel_env.antimono; apply HsemΓ; omega
  have Hsem_expr := He _ _ _ HsemΓ
  rw [log_rel_expr] at Hsem_expr
  have ⟨v₁, Hstep₁, Hsem_value⟩ := Hsem_expr i₁ (by omega) _ Hvalue₀ Hstep₀
  --
  --
  -- γ₁(b₁) ⇝* bv₁
  -- (x ↦ bv₁, γ₁)(e₁) ⇝* v₁
  -- ———————————————————————————————
  -- lets x = γ₁(b₁) in γ₁(e₁) ⇝* v₁
  exists v₁
  constructor
  . simp
    -- left
    apply stepn.trans
    apply stepn.grounded.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.lets _ Hlc₁.right) (typing.grounded_at_dyn _ _ _ _ HSτb₁) HstepBind₁
    -- head
    have HEqSubst₁ : opening 0 bv₁ (multi_subst γ₁ e₁) = multi_subst (bv₁ :: γ₁) ({0 ↦ Γ.length} e₁) :=
      by
      rw [multi_subst, ← comm.multi_subst_subst _ _ _ _ _ _ Hmulti_wf₁]
      rw [comm.multi_subst_opening _ _ _ _ _ Hmulti_wf₁]
      rw [HEq₁, intros.subst]
      apply closed.inc; apply Hclosed₁.right; omega
      omega; omega; apply HclosedBind₁
    rw [← HEqSubst₁] at Hstep₁
    apply stepn.multi _ _ _ _ Hstep₁
    apply step_lvl.pure id; apply ctx𝕄.hole
    constructor; apply HlcBind₁; apply Hlc₁.right
    apply head.lets; apply HvalueBind₁
  . apply log_rel_value.antimono
    apply Hsem_value; omega

lemma compatibility.fix₁.induction :
  ∀ k f₀ f₁ τ𝕒 τ𝕓,
    log_rel_value k f₀ f₁ (.arrow (.arrow τ𝕒 τ𝕓 ∅) (.arrow τ𝕒 τ𝕓 ∅) ∅) →
    log_rel_value k
      (.lam (.app₁ (.app₁ f₀ (.fix₁ f₀)) (.bvar 0)))
      (.lam (.app₁ (.app₁ f₁ (.fix₁ f₁)) (.bvar 0)))
    (.arrow τ𝕒 τ𝕓 ∅) :=
  by
  intros k f₀ f₁ τ𝕒 τ𝕓 Hsem_value_fix
  have ⟨HvalueFix₀, HvalueFix₁⟩ := log_rel_value.syntactic.value _ _ _ _ Hsem_value_fix
  have ⟨HτFix₀, HτFix₁⟩ := log_rel_value.syntactic.typing _ _ _ _ Hsem_value_fix
  have ⟨HlcFix₀, HclosedFix₀⟩ := typing.wf _ _ _ _ _ HτFix₀
  have ⟨HlcFix₁, HclosedFix₁⟩ := typing.wf _ _ _ _ _ HτFix₁
  have Hwbt: wbt 𝟚 τ𝕒 := by cases HvalueFix₀ <;> cases HτFix₀; next Hwbt _ => apply Hwbt.right.left
  have Hτ₀ : typing [] 𝟚 (.lam (.app₁ (.app₁ f₀ (.fix₁ f₀)) (.bvar 0))) (.arrow τ𝕒 τ𝕓 ∅) ∅ :=
    by
    apply typing.lam; rw [← union_pure_left ∅, ← union_pure_left ∅]
    apply typing.app₁; rw [← union_pure_left ∅, ← union_pure_left ∅, identity.opening _ _ _ (by simp; apply HlcFix₀)]
    apply typing.weakening.singleton
    apply typing.app₁; apply HτFix₀
    apply typing.fix₁; simp; rfl; apply HτFix₀
    apply typing.fvar; simp; apply Hwbt; apply Hwbt
    simp; apply HclosedFix₀
  have Hτ₁ : typing [] 𝟚 (.lam (.app₁ (.app₁ f₁ (.fix₁ f₁)) (.bvar 0))) (.arrow τ𝕒 τ𝕓 ∅) ∅ :=
    by
    apply typing.lam; rw [← union_pure_left ∅, ← union_pure_left ∅]
    apply typing.app₁; rw [← union_pure_left ∅, ← union_pure_left ∅, identity.opening _ _ _ (by simp; apply HlcFix₁)]
    apply typing.weakening.singleton
    apply typing.app₁; apply HτFix₁
    apply typing.fix₁; simp; rfl; apply HτFix₁
    apply typing.fvar; simp; apply Hwbt; apply Hwbt
    simp; apply HclosedFix₁
  induction k
  case zero =>
    rw [log_rel_value]
    constructor; apply Hτ₀
    constructor; apply Hτ₁
    intro z Hindexz argv₀ argv₁ Hsem_value_arg
    rw [log_rel_expr]
    intro j Hindexj; omega
  case succ k IH =>
    rw [log_rel_value]
    constructor; apply Hτ₀
    constructor; apply Hτ₁
    intros s Hindexs argv₀ argv₁ Hsem_value_arg
    have ⟨HvalueArg₀, HvalueArg₁⟩ := log_rel_value.syntactic.value _ _ _ _ Hsem_value_arg
    have ⟨HτArg₀, HτArg₁⟩ := log_rel_value.syntactic.typing _ _ _ _ Hsem_value_arg
    have ⟨HlcArg₀, HclosedArg₀⟩ := typing.wf _ _ _ _ _ HτArg₀
    have ⟨HlcArg₁, HclosedArg₁⟩ := typing.wf _ _ _ _ _ HτArg₁
    rw [log_rel_expr]
    intro j Hindexj v₀ Hvalue₀ Hstep₀
    --
    --
    -- (λx.f₀ @ fix f₀ @ x) @ argv₀ ⇝ ⟦j⟧ v₀
    -- ——————————————————————————————————————————
    -- i + 2 = j
    -- f₀ @ (λx.f₀ @ fix f₀ @ x) @ argv₀ ⇝ ⟦i⟧ v₀
    have ⟨i, HEqj, Hstep₀⟩ :=
      stepn_indexed.refine.fix₁.induction _ _ _ _ HvalueFix₀ HvalueArg₀ Hvalue₀ (
        by
        simp; apply typing.grounded_at_dyn
        apply HτFix₀
      ) Hstep₀
    --
    --
    -- f₀ @ (λx.f₀ @ fix f₀ @ x) @ argv₀ ⇝ ⟦i⟧ v₀
    -- ——————————————————————————————————————————
    -- i₀ + i₁ = i
    -- f₀ @ (λx.f₀ @ fix f₀ @ x) ⇝ ⟦i₀⟧ fv₀
    -- fv₀ @ argv₀ ⇝ ⟦i₁⟧ fv₀
    have ⟨i₀, z, i₁, fv₀, r₀, HEqj, HvalueFun₀, _, HstepFun₀, HstepArg₀, Hstep₀⟩ :=
      stepn_indexed.refine.app₁ _ _ _ _ Hvalue₀ (
          by
          simp; constructor
          apply typing.grounded_at_dyn; apply HτFix₀
          apply typing.grounded_at_dyn; apply HτArg₀
      ) Hstep₀
    have ⟨HEqv, Hz⟩ := stepn_indexed.value_impl_termination _ _ _ HvalueArg₀ HstepArg₀
    rw [← HEqv] at Hstep₀
    --
    --
    -- (f₀, f₁) ∈ 𝓥⟦(τ𝕒 → τ𝕓) → (τ𝕒 → τ𝕓)⟧{k + 1}
    -- (λx.f₀ @ fix f₀ @ x, λx.f₁ @ fix f₁ @ x) ∈ 𝓥⟦τ𝕒 → τ𝕓⟧{k}
    -- —————————————————————————————————————————————————————————————————————
    -- (f₀ @ (λx.f₀ @ fix f₀ @ x), f₁ @ (λx.f₁ @ fix f₁ @ x)) ∈ 𝓔⟦τ𝕒 → τ𝕓⟧{k}
    have Hsem_expr_fun :
      log_rel_expr k
        (.app₁ f₀ (.lam (.app₁ (.app₁ f₀ (.fix₁ f₀)) (.bvar 0))))
        (.app₁ f₁ (.lam (.app₁ (.app₁ f₁ (.fix₁ f₁)) (.bvar 0))))
      (.arrow τ𝕒 τ𝕓 ∅) :=
      by
      apply log_rel_value.apply
      apply log_rel_value.antimono; apply Hsem_value_fix; omega
      apply IH; apply log_rel_value.antimono; apply Hsem_value_fix; omega
    --
    --
    -- f₀ @ (λx.f₀ @ fix f₀ @ x) ⇝ ⟦i₀⟧ fv₀
    -- (f₀ @ (λx.f₀ @ fix f₀ @ x), f₁ @ (λx.f₁ @ fix f₁ @ x)) ∈ 𝓔⟦τ𝕒 → τ𝕓⟧{k}
    -- —————————————————————————————————————————————————————————————————————
    -- f₁ @ (λx.f₁ @ fix f₁ @ x) ⇝* fv₁
    -- (fv₀, fv₁) ∈ 𝓥⟦τ𝕒 → τ𝕓⟧{k - i₀}
    rw [log_rel_expr] at Hsem_expr_fun
    have ⟨fv₁, HstepFun₁, Hsem_value_fun⟩ := Hsem_expr_fun i₀ (by omega) _ HvalueFun₀ HstepFun₀
    --
    --
    -- (fv₀, fv₁) ∈ 𝓥⟦τ𝕒 → τ𝕓⟧{k - i₀}
    -- (argv₀, argv₁) ∈ 𝓥⟦τ𝕒⟧{s}
    -- —————————————————————————————————————————————
    -- (fv₀ @ argv₀, fv₁ @ argv₁) ∈ 𝓔⟦τ𝕓⟧{s - i₀ - 1}
    have Hsem_value_fun : log_rel_value (s - i₀ - 1) fv₀ fv₁ (τ𝕒.arrow τ𝕓 ∅) := log_rel_value.antimono _ _ _ _ _ Hsem_value_fun (by omega)
    have Hsem_value_arg : log_rel_value (s - i₀ - 1) argv₀ argv₁ τ𝕒 := log_rel_value.antimono _ _ _ _ _ Hsem_value_arg (by omega)
    have Hsem_expr := log_rel_value.apply _ _ _ _ _ _ _ Hsem_value_fun Hsem_value_arg
    --
    --
    -- (fv₀ @ argv₀, fv₁ @ argv₁) ∈ 𝓔⟦τ𝕓⟧{s - i₀ - 1}
    -- fv₀ @ argv₀ ⇝ ⟦i₁⟧ v₀
    -- —————————————————————————————————————————————
    -- fv₁ @ argv₁ ⇝* v₁
    -- (v₀, v₁) ∈ 𝓥⟦τ𝕓⟧{s - i₀ - i₁ - 1}
    simp only [log_rel_expr] at Hsem_expr
    have ⟨v₁, Hstep₁, Hsem_value⟩ := Hsem_expr i₁ (by omega) v₀ Hvalue₀ Hstep₀
    --
    --
    -- f₁ @ (λx.f₁ @ fix f₁ @ x) ⇝* fv₁
    -- fv₁ @ argv₁ ⇝* v₁
    -- ——————————————————————————————————
    -- (λx.f₁ @ fix f₁ @ x) @ argv₁ ⇝* v₁
    exists v₁
    constructor
    . -- head₀
      apply stepn.multi
      apply step_lvl.pure id; apply ctx𝕄.hole
      simp; constructor
      apply lc.inc; apply HlcFix₁; omega
      apply HlcArg₁
      apply head.app₁; apply HvalueArg₁
      simp [identity.opening _ _ _ HlcFix₁]
      -- head₁
      apply stepn.multi
      apply step.grounded.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.appl₁ _ (lc.value _ HvalueArg₁))
      simp; apply typing.grounded_at_dyn; apply HτFix₁
      apply step.grounded.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.appr₁ _ HvalueFix₁)
      simp; apply typing.grounded_at_dyn; apply HτFix₁
      apply step_lvl.pure id; apply ctx𝕄.hole
      apply HlcFix₁
      apply head.fix₁; apply HvalueFix₁
      -- left
      apply stepn.trans
      apply stepn.grounded.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.appl₁ _ _)
      simp; apply typing.grounded_at_dyn; apply HτFix₁; apply HstepFun₁
      apply HlcArg₁
      -- head₂
      apply Hstep₁
    . apply log_rel_value.antimono
      apply Hsem_value; omega

-- Γ ⊧ f₀ ≤𝑙𝑜𝑔 f₁ : (τ𝕒 → τ𝕓) → τ𝕒 → τ𝕓
-- ————————————————————————————————————
-- Γ ⊧ fix f₀ ≤𝑙𝑜𝑔 fix f₁ : τ𝕒 → τ𝕓
lemma compatibility.fix₁ :
  ∀ Γ f₀ f₁ τ𝕒 τ𝕓,
    log_rel_typing Γ f₀ f₁ (.arrow (.arrow τ𝕒 τ𝕓 ∅) (.arrow τ𝕒 τ𝕓 ∅) ∅) →
    log_rel_typing Γ (.fix₁ f₀) (.fix₁ f₁) (.arrow τ𝕒 τ𝕓 ∅) :=
  by
  intros Γ f₀ f₁ τ𝕒 τ𝕓 Hf
  have ⟨HτFix₀, HτFix₁, Hf⟩ := Hf
  have Hτ₀ : typing Γ 𝟚 (.fix₁ f₀) (.arrow τ𝕒 τ𝕓 ∅) ∅ := by apply typing.fix₁; simp; rfl; apply HτFix₀
  have Hτ₁ : typing Γ 𝟚 (.fix₁ f₁) (.arrow τ𝕒 τ𝕓 ∅) ∅ := by apply typing.fix₁; simp; rfl; apply HτFix₁
  constructor; apply Hτ₀
  constructor; apply Hτ₁
  intros k γ₀ γ₁ HsemΓ
  have ⟨HSτFix₀, HSτFix₁⟩ := log_rel_env.multi_subst.typing _ _ _ _ _ _ _ HτFix₀ HτFix₁ HsemΓ
  simp only [multi_subst.fix₁, log_rel_expr]
  intros j Hindexj v₀ Hvalue₀ Hstep₀
  --
  --
  -- fix γ₀(f₀) ⇝ ⟦j⟧ v₀
  -- ——————————————————————————
  -- i₀ + 1 = j
  -- γ₀(f₀) ⇝ ⟦i₀⟧ fv₀
  -- v₀ = λx.fv₀ @ fix fv₀ @ x
  have ⟨i₀, fv₀, HEqj, HvalueFix₀, HstepFix₀, HEqv₀⟩ :=
    stepn_indexed.refine.fix₁ _ _ _ Hvalue₀ (
      by
      simp; apply typing.grounded_at_dyn
      apply HSτFix₀
    ) Hstep₀
  rw [HEqv₀]
  --
  --
  -- γ₀(f₀) ⇝ ⟦i₀⟧ fv₀
  -- (γ₀(f₀), γ₁(f₁)) ∈ 𝓔⟦τ𝕓⟧{k}
  -- ——————————————————————————
  -- γ₁(f₁) ⇝* fv₁
  -- (fv₀, fv₁) ∈ 𝓥⟦τ𝕓⟧{k - i₀}
  simp only [log_rel_expr] at Hf
  have ⟨fv₁, HstepFix₁, Hsem_value_fun⟩ := Hf _ _ _ HsemΓ i₀ (by omega) _ HvalueFix₀ HstepFix₀
  have ⟨HvalueFix₀, HvalueFix₁⟩ := log_rel_value.syntactic.value _ _ _ _ Hsem_value_fun
  --
  --
  -- γ₁(f₁) ⇝* fv₁
  -- ———————————————————————————————————
  -- fix γ₁(f₁) ⇝* λx.fv₁ @ fix fv₁ @ x
  exists .lam (.app₁ (.app₁ fv₁ (.fix₁ fv₁)) (.bvar 0))
  constructor
  . -- left
    apply stepn.trans
    apply stepn.grounded.congruence_under_ctx𝔹 _ _ _ ctx𝔹.fix₁
    apply typing.grounded_at_dyn; apply HSτFix₁; apply HstepFix₁
    -- head
    apply stepn.multi _ _ _ _ (stepn.refl _)
    apply step_lvl.pure id; apply ctx𝕄.hole
    simp; apply lc.value; apply HvalueFix₁
    apply head.fix₁; apply HvalueFix₁
  . apply compatibility.fix₁.induction
    apply log_rel_value.antimono
    apply Hsem_value_fun; omega
