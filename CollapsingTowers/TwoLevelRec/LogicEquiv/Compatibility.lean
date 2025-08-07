import CollapsingTowers.TwoLevelRec.LogicEquiv.LogicRelation

-- Γ ⊧ x ≤𝑙𝑜𝑔 x : Γ(x)
lemma compatibility.fvar :
  ∀ Γ x τ,
    binds x (τ, 𝟙) Γ →
    logic_rel_typing Γ (.fvar x) (.fvar x) τ :=
  by
  intros Γ x τ Hbinds
  constructor; constructor
  . constructor
  . simp [getr_exists_iff_index_lt_length]
    exists τ, 𝟙
  constructor; constructor
  . constructor
  . simp [getr_exists_iff_index_lt_length]
    exists τ, 𝟙
  intros k γ₀ γ₁ HsemΓ
  simp only [logic_rel_expr]
  intros z Hindexz v₀ Hvalue₀ Hstep₀
  exists multi_subst γ₁ (.fvar x)
  constructor
  . apply pure_stepn.refl
  . have Hsem_value := logic_rel_env.binds_logic_rel_value _ _ _ _ _ _ HsemΓ Hbinds
    have ⟨Hvalue₀, Hvalue₁⟩ := logic_rel_value.syntactic_value _ _ _ _ Hsem_value
    have ⟨HEqv, Hz⟩ := pure_stepn_indexed.value_impl_termination _ _ _ Hvalue₀ Hstep₀
    rw [← HEqv, Hz]; apply Hsem_value

-- Γ ⊧ n ≤𝑙𝑜𝑔 n : ℕ
lemma compatibility.lit :
  ∀ Γ n, logic_rel_typing Γ (.lit n) (.lit n) .nat :=
  by
  intros _ n
  constructor; constructor
  . constructor
  . constructor
  constructor; constructor
  . constructor
  . constructor
  intros k γ₀ γ₁ semΓ
  simp only [logic_rel_expr]
  intros z Hindexz v₀ Hvalue₀ Hstep₀
  exists .lit n
  constructor
  . simp; apply pure_stepn.refl
  . simp at Hstep₀
    have ⟨HEqv, Hz⟩ := pure_stepn_indexed.value_impl_termination _ _ _ (value.lit n) Hstep₀
    simp [← HEqv, Hz]

-- x ↦ τ𝕒, Γ ⊧ e₀ ≤𝑙𝑜𝑔 e₁ : τ𝕓
-- ——————————————————————————————————————————
-- Γ ⊧ λx.e₀ ≤𝑙𝑜𝑔 λx.e₁ : τ𝕒 → τ𝕓
lemma compatibility.lam :
  ∀ Γ e₀ e₁ τ𝕒 τ𝕓,
    closed_at (.lam e₀) Γ.length →
    closed_at (.lam e₁) Γ.length →
    logic_rel_typing ((τ𝕒, 𝟙) :: Γ) ({0 ↦ Γ.length} e₀) ({0 ↦ Γ.length} e₁) τ𝕓 →
    logic_rel_typing Γ (.lam e₀) (.lam e₁) (.arrow τ𝕒 τ𝕓 ∅) :=
  by
  intros Γ e₀ e₁ τ𝕒 τ𝕓 Hclosed₀ Hclosed₁ He
  have ⟨Hwf₀, Hwf₁, He⟩ := He
  have Hlc₀ : lc (.lam e₀) := by apply (lc.under_opening _ _ _).mp; apply Hwf₀.left
  have Hlc₁ : lc (.lam e₁) := by apply (lc.under_opening _ _ _).mp; apply Hwf₁.left
  constructor; constructor
  apply Hlc₀; apply Hclosed₀
  constructor; constructor
  apply Hlc₁; apply Hclosed₁
  intros k γ₀ γ₁ HsemΓ
  have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := logic_rel_env.multi_wf _ _ _ _ HsemΓ
  have ⟨HEq₀, HEq₁⟩ := logic_rel_env.length _ _ _ _ HsemΓ
  have Hlc₀ : lc (.lam (multi_subst γ₀ e₀)) :=
    by apply lc.under_multi_subst; apply Hmulti_wf₀; apply Hlc₀
  have Hlc₁ : lc (.lam (multi_subst γ₁ e₁)) :=
    by apply lc.under_multi_subst; apply Hmulti_wf₁; apply Hlc₁
  have Hclosed₀ : closed (.lam (multi_subst γ₀ e₀)) :=
    by apply closed.under_multi_subst; apply Hmulti_wf₀; rw [HEq₀]; apply Hclosed₀
  have Hclosed₁ : closed (.lam (multi_subst γ₁ e₁)) :=
    by apply closed.under_multi_subst; apply Hmulti_wf₁; rw [HEq₁]; apply Hclosed₁
  rw [logic_rel_expr]
  intros z Hindexz v₀ HvalueRes₀ Hstep₀
  --
  --
  -- λx.γ₀(e₀) ⇾ ⟦z⟧ v₀
  -- ——————————————————
  -- z = 0
  -- v₀ = λx.γ₀(e₀)
  simp at Hstep₀
  have ⟨HEqv₀, HEqz⟩ := pure_stepn_indexed.value_impl_termination _ _ _ (value.lam _ Hlc₀) Hstep₀
  exists multi_subst γ₁ (.lam e₁)
  constructor; apply pure_stepn.refl
  simp only [← HEqv₀, HEqz, multi_subst.lam, logic_rel_value]
  constructor; constructor
  apply Hlc₀; apply Hclosed₀
  constructor; constructor
  apply Hlc₁; apply Hclosed₁
  intros k Hindexk argv₀ argv₁ Hsem_value_arg
  have ⟨HvalueArg₀, HvalueArg₁⟩ := logic_rel_value.syntactic_value _ _ _ _ Hsem_value_arg
  have ⟨HwfArg₀, HwfArg₁⟩ := logic_rel_value.wf _ _ _ _ Hsem_value_arg
  rw [logic_rel_expr]
  intros j Hindexj v₀ HvalueRes₀ Hstep₀
  --
  --
  -- λx.γ₀(e₀) @ argv₀ ⇾ ⟦j⟧ v₀
  -- ——————————————————————————————————
  -- j = i + 1
  -- ⟦x ↦ argv₀⟧γ₀(e₀) ⇾ ⟦i⟧ v₀
  have ⟨i, HEqj, HstepRes₀⟩ := pure_stepn_indexed.refine.lam _ _ _ _ Hlc₀ HvalueArg₀ HvalueRes₀ Hstep₀
  --
  --
  -- ⟦x ↦ argv₀⟧γ₀(e₀) ⇾ ⟦i⟧ v₀
  -- (⟦x ↦ argv₀⟧γ₀(e₀), ⟦x ↦ argv₁⟧γ₁(e₁)) ∈ 𝓔⟦τ𝕓⟧⟦k⟧
  -- —————————————————————————————————————————————————
  -- ⟦x ↦ argv₁⟧γ₁(e₁) ⇾* v₁
  -- (v₀, v₁) ∈ 𝓥⟦τ𝕓⟧⟦k - i⟧
  have HEqSubst₀ : opening 0 argv₀ (multi_subst γ₀ e₀) = multi_subst (argv₀ :: γ₀) ({0 ↦ Γ.length} e₀) :=
    by
    rw [multi_subst, ← comm.multi_subst_subst _ _ _ _ _ _ Hmulti_wf₀]
    rw [comm.multi_subst_opening _ _ _ _ _ Hmulti_wf₀]
    rw [HEq₀, intros.subst]
    apply closed.inc; apply Hclosed₀; omega
    omega; omega; apply HwfArg₀.right
  rw [HEqSubst₀] at HstepRes₀
  have HsemΓ : logic_rel_env k (argv₀ :: γ₀) (argv₁ :: γ₁) ((τ𝕒, 𝟙) :: Γ) :=
    by
    apply logic_rel_env.cons; apply Hsem_value_arg
    apply logic_rel_env.weakening; apply HsemΓ; omega
  have Hsem_expr := He _ _ _ HsemΓ
  rw [logic_rel_expr] at Hsem_expr
  have ⟨v₁, HstepRes₁, Hsem_value⟩ := Hsem_expr i (by omega) _ HvalueRes₀ HstepRes₀
  --
  --
  -- ⟦x ↦ argv₁⟧γ₁(e₁) ⇾* v₁
  -- ————————————————————————
  -- λx.γ₁(e₁) @ argv₁ ⇾* v₁
  exists v₁
  constructor
  . have HEqSubst₁ : opening 0 argv₁ (multi_subst γ₁ e₁) = multi_subst (argv₁ :: γ₁) ({0 ↦ Γ.length} e₁) :=
      by
      rw [multi_subst, ← comm.multi_subst_subst _ _ _ _ _ _ Hmulti_wf₁]
      rw [comm.multi_subst_opening _ _ _ _ _ Hmulti_wf₁]
      rw [HEq₁, intros.subst]
      apply closed.inc; apply Hclosed₁; omega
      omega; omega; apply HwfArg₁.right
    rw [← HEqSubst₁] at HstepRes₁
    apply pure_stepn.multi _ _ _ _ HstepRes₁
    apply pure_step.pure id; apply ctx𝕄.hole
    constructor; apply Hlc₁; apply lc.value; apply HvalueArg₁
    apply head.app₁; apply HvalueArg₁
  . apply logic_rel_value.weakening
    apply Hsem_value; omega

-- Γ ⊧ f₀ ≤𝑙𝑜𝑔 f₁ : τ𝕒 → τ𝕓
-- Γ ⊧ arg₀ ≤𝑙𝑜𝑔 arg₁ : τ𝕒
-- —————————————————————————————————
-- Γ ⊧ f₀ @ arg₀ ≤𝑙𝑜𝑔 f₁ @ arg₁ : τ𝕓
lemma compatibility.app₁ :
  ∀ Γ f₀ f₁ arg₀ arg₁ τ𝕒 τ𝕓,
    logic_rel_typing Γ f₀ f₁ (.arrow τ𝕒 τ𝕓 ∅) →
    logic_rel_typing Γ arg₀ arg₁ τ𝕒 →
    logic_rel_typing Γ (.app₁ f₀ arg₀) (.app₁ f₁ arg₁) τ𝕓 :=
  by
  intros Γ f₀ f₁ arg₀ arg₁ τ𝕒 τ𝕓 Hf Harg
  have ⟨HwfFun₀, HwfFun₁, Hf⟩ := Hf
  have ⟨HwfArg₀, HwfArg₁, Harg⟩ := Harg
  constructor; constructor
  . constructor; apply HwfFun₀.left; apply HwfArg₀.left
  . constructor; apply HwfFun₀.right; apply HwfArg₀.right
  constructor; constructor
  . constructor; apply HwfFun₁.left; apply HwfArg₁.left
  . constructor; apply HwfFun₁.right; apply HwfArg₁.right
  intros k γ₀ γ₁ HsemΓ
  have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := logic_rel_env.multi_wf _ _ _ _ HsemΓ
  rw [logic_rel_expr]
  intros j Hindex v₀ HvalueRes₀ Hstep₀
  --
  --
  -- γ₀(f₀) @ γ₀(arg₀) ⇾ ⟦j⟧ v₀
  -- ———————————————————————————
  -- i₀ + i₁ + i₂ = j
  -- γ₀(f₀) ⇾ ⟦i₀⟧ fv₀
  -- γ₀(f₀) ⇾ ⟦i₁⟧ argv₀
  -- fv₀ @ argv₀ ⇾ ⟦i₂⟧ v₀
  simp at Hstep₀
  have ⟨i₀, i₁, i₂, fv₀, argv₀, HEqj, HvalueFun₀, HvalueArg₀, HstepFun₀, HstepArg₀, HstepRes₀⟩ := pure_stepn_indexed.refine.app₁ _ _ _ _ HvalueRes₀ Hstep₀
  --
  --
  -- γ₀(f₀) ⇾ ⟦i₀⟧ fv₀
  -- Γ ⊧ f₀ ≤𝑙𝑜𝑔 f₁ : τ𝕒 → τ𝕓
  -- ———————————————————————————————
  -- γ₁(f₁) ⇾* fv₁
  -- (fv₀, fv₁) ∈ 𝓥⟦τ𝕒 → τ𝕓⟧⟦k - i₀⟧
  simp only [logic_rel_expr] at Hf
  have ⟨fv₁, HstepFun₁, Hsem_value_fun⟩ := Hf _ _ _ HsemΓ i₀ (by omega) _ HvalueFun₀ HstepFun₀
  have ⟨HvalueFun₀, HvalueFun₁⟩ := logic_rel_value.syntactic_value _ _ _ _ Hsem_value_fun
  --
  --
  -- γ₀(arg₀) ⇾ ⟦i₁⟧ argv₀
  -- Γ ⊧ arg₀ ≤𝑙𝑜𝑔 arg₁ : τ𝕒
  -- —————————————————————————————
  -- γ₁(arg₁) ⇾* argv₁
  -- (argv₀, argv₁) ∈ 𝓥⟦τ𝕒⟧⟦k - i₁⟧
  simp only [logic_rel_expr] at Harg
  have ⟨argv₁, HstepArg₁, Hsem_value_arg⟩ := Harg _ _ _ HsemΓ i₁ (by omega) _ HvalueArg₀ HstepArg₀
  --
  --
  -- (fv₀, fv₁) ∈ 𝓥⟦τ𝕒 → τ𝕓⟧⟦k - i₀⟧
  -- (argv₀, argv₁) ∈ 𝓥⟦τ𝕒⟧⟦k - i₁⟧
  -- ———————————————————————————————————————————————
  -- (fv₀ @ argv₀, fv₁ @ argv₁) ∈ 𝓔⟦τ𝕓⟧⟦k - i₀ - i₁⟧
  have Hsem_value_fun : logic_rel_value (k - i₀ - i₁) fv₀ fv₁ (τ𝕒.arrow τ𝕓 ∅) := logic_rel_value.weakening _ _ _ _ _ Hsem_value_fun (by omega)
  have Hsem_value_arg : logic_rel_value (k - i₀ - i₁) argv₀ argv₁ τ𝕒 := logic_rel_value.weakening _ _ _ _ _ Hsem_value_arg (by omega)
  have Hsem_expr := logic_rel_value.apply _ _ _ _ _ _ _ Hsem_value_fun Hsem_value_arg
  --
  --
  -- (fv₀ @ argv₀, fv₁ @ argv₁) ∈ 𝓔⟦τ𝕓⟧⟦k - i₀ - i₁⟧
  -- fv₀ @ argv₀ ⇾ ⟦i₂⟧ v₀
  -- ———————————————————————————————————————————————
  -- fv₁ @ argv₁ ⇾* v₁
  -- (v₀, v₁) ∈ 𝓥⟦τ𝕓⟧⟦k - i₀ - i₁ - i₂⟧
  simp only [logic_rel_expr] at Hsem_expr
  have ⟨v₁, HstepRes₁, Hsem_value⟩ := Hsem_expr i₂ (by omega) v₀ HvalueRes₀ HstepRes₀
  --
  --
  -- γ₁(f₁) ⇾* fv₁
  -- γ₁(arg₁) ⇾* argv₁
  -- fv₁ @ argv₁ ⇾* v₁
  -- ————————————————————————
  -- γ₁(f₁) @ γ₁(arg₁) ⇾* v₁
  exists v₁; constructor
  . simp
    apply pure_stepn.trans
    -- left
    apply pure_stepn.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.appl₁ _ _) HstepFun₁
    apply lc.under_multi_subst; apply Hmulti_wf₁; apply HwfArg₁.left
    -- right
    apply pure_stepn.trans
    apply pure_stepn.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.appr₁ _ HvalueFun₁) HstepArg₁
    -- head
    apply HstepRes₁
  . apply logic_rel_value.weakening
    apply Hsem_value; omega

-- Γ ⊧ b₀ ≤𝑙𝑜𝑔 b₁ : τ𝕒
-- x ↦ τ𝕒, Γ ⊧ e₀ ≤𝑙𝑜𝑔 e₁ : τ𝕓
-- —————————————————————————————————————————————————
-- Γ ⊧ lets x = b₀ in e₀ ≤𝑙𝑜𝑔 lets x = b₁ in e₁ : τ𝕓
lemma compatibility.lets :
  ∀ Γ b₀ b₁ e₀ e₁ τ𝕒 τ𝕓,
    closed_at (.lets b₀ e₀) Γ.length →
    closed_at (.lets b₁ e₁) Γ.length →
    logic_rel_typing Γ b₀ b₁ τ𝕒 →
    logic_rel_typing ((τ𝕒, 𝟙) :: Γ) ({0 ↦ Γ.length} e₀) ({0 ↦ Γ.length} e₁) τ𝕓 →
    logic_rel_typing Γ (.lets b₀ e₀) (.lets b₁ e₁) τ𝕓 :=
  by
  intros Γ b₀ b₁ e₀ e₁ τ𝕒 τ𝕓 Hclosed₀ Hclosed₁ Hb He
  have ⟨HwfBind₀, HwfBind₁, Hb⟩ := Hb
  have ⟨Hwf₀, Hwf₁, He⟩ := He
  have Hlc₀ : lc (.lets b₀ e₀) :=
    by
    constructor; apply HwfBind₀.left
    apply (lc.under_opening _ _ _).mp; apply Hwf₀.left
  have Hlc₁ : lc (.lets b₁ e₁) :=
    by
    constructor; apply HwfBind₁.left
    apply (lc.under_opening _ _ _).mp; apply Hwf₁.left
  constructor; constructor
  apply Hlc₀; apply Hclosed₀
  constructor; constructor
  apply Hlc₁; apply Hclosed₁
  intros k γ₀ γ₁ HsemΓ
  have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := logic_rel_env.multi_wf _ _ _ _ HsemΓ
  have ⟨HEq₀, HEq₁⟩ := logic_rel_env.length _ _ _ _ HsemΓ
  have Hlc₀ : lc (.lets (multi_subst γ₀ b₀) (multi_subst γ₀ e₀)) :=
    by
    rw [← multi_subst.lets]; apply lc.under_multi_subst
    apply Hmulti_wf₀; apply Hlc₀
  have Hlc₁ : lc (.lets (multi_subst γ₁ b₁) (multi_subst γ₁ e₁)) :=
    by
    rw [← multi_subst.lets]; apply lc.under_multi_subst
    apply Hmulti_wf₁; apply Hlc₁
  have Hclosed₀ : closed (.lets (multi_subst γ₀ b₀) (multi_subst γ₀ e₀)) :=
    by
    rw [← multi_subst.lets]; apply closed.under_multi_subst
    apply Hmulti_wf₀; rw [HEq₀]; apply Hclosed₀
  have Hclosed₁ : closed (.lets (multi_subst γ₁ b₁) (multi_subst γ₁ e₁)) :=
    by
    rw [← multi_subst.lets]; apply closed.under_multi_subst
    apply Hmulti_wf₁; rw [HEq₁]; apply Hclosed₁
  rw [logic_rel_expr]
  intros j Hindex v₀ HvalueRes₀ Hstep₀
  --
  --
  -- lets x = γ₀(b₀) in γ₀(e₀) ⇾ ⟦j⟧ v₀
  -- ——————————————————————————————————
  -- i₀ + 1 + i₁ = j
  -- γ₀(b₀) ⇾ ⟦i₀⟧ bv₀
  -- ⟦x ↦ bv₀⟧γ₀(e₀) ⇾ ⟦i₁⟧ v₀
  simp at Hstep₀
  have ⟨i₀, i₁, bv₀, HEqj, HvalueBind₀, HstepBind₀, HstepRes₀⟩ := pure_stepn_indexed.refine.lets _ _ _ _ HvalueRes₀ Hstep₀
  --
  --
  -- γ₀(b₀) ⇾ ⟦i₀⟧ bv₀
  -- Γ ⊧ b₀ ≤𝑙𝑜𝑔 b₁ : τ𝕒 → τ𝕓
  -- ———————————————————————————————
  -- γ₁(b₁) ⇾* bv₁
  -- (bv₀, bv₁) ∈ 𝓥⟦τ𝕒 → τ𝕓⟧⟦k - i₀⟧
  simp only [logic_rel_expr] at Hb
  have ⟨bv₁, HstepBind₁, Hsem_value_bind⟩ := Hb _ _ _ HsemΓ i₀ (by omega) _ HvalueBind₀ HstepBind₀
  have ⟨HvalueBind₀, HvalueBind₁⟩ := logic_rel_value.syntactic_value _ _ _ _ Hsem_value_bind
  have ⟨HwfBind₀, HwfBind₁⟩ := logic_rel_value.wf _ _ _ _ Hsem_value_bind
  --
  --
  -- ⟦x ↦ bv₀⟧γ₀(e₀) ⇾ ⟦i₁⟧ v₀
  -- (⟦x ↦ bv₀⟧γ₀(e₀), ⟦x ↦ bv₁⟧γ₁(e₁)) ∈ 𝓔⟦τ𝕓⟧⟦k - i₀⟧
  -- —————————————————————————————————————————————————
  -- ⟦x ↦ bv₁⟧γ₁(e₁) ⇾* v₁
  -- (v₀, v₁) ∈ 𝓥⟦τ𝕓⟧⟦k - i₀ - i₁⟧
  have HEqSubst₀ : opening 0 bv₀ (multi_subst γ₀ e₀) = multi_subst (bv₀ :: γ₀) ({0 ↦ Γ.length} e₀) :=
    by
    rw [multi_subst, ← comm.multi_subst_subst _ _ _ _ _ _ Hmulti_wf₀]
    rw [comm.multi_subst_opening _ _ _ _ _ Hmulti_wf₀]
    rw [HEq₀, intros.subst]
    apply closed.inc; apply Hclosed₀.right; omega
    omega; omega; apply HwfBind₀.right
  rw [HEqSubst₀] at HstepRes₀
  have HsemΓ : logic_rel_env (k - i₀) (bv₀ :: γ₀) (bv₁ :: γ₁) ((τ𝕒, 𝟙) :: Γ) :=
    by
    apply logic_rel_env.cons; apply Hsem_value_bind
    apply logic_rel_env.weakening; apply HsemΓ; omega
  have Hsem_expr := He _ _ _ HsemΓ
  rw [logic_rel_expr] at Hsem_expr
  have ⟨v₁, HstepRes₁, Hsem_value⟩ := Hsem_expr i₁ (by omega) _ HvalueRes₀ HstepRes₀
  --
  --
  -- γ₁(b₁) ⇾* bv₁
  -- ⟦x ↦ bv₁⟧γ₁(e₁) ⇾* v₁
  -- ———————————————————————————————
  -- lets x = γ₁(b₁) in γ₁(e₁) ⇾* v₁
  exists v₁
  constructor
  . simp
    apply pure_stepn.trans
    -- left
    apply pure_stepn.congruence_under_ctx𝔹 _ _ _ (ctx𝔹.lets _ Hlc₁.right) HstepBind₁
    -- head
    have HEqSubst₁ : opening 0 bv₁ (multi_subst γ₁ e₁) = multi_subst (bv₁ :: γ₁) ({0 ↦ Γ.length} e₁) :=
      by
      rw [multi_subst, ← comm.multi_subst_subst _ _ _ _ _ _ Hmulti_wf₁]
      rw [comm.multi_subst_opening _ _ _ _ _ Hmulti_wf₁]
      rw [HEq₁, intros.subst]
      apply closed.inc; apply Hclosed₁.right; omega
      omega; omega; apply HwfBind₁.right
    rw [← HEqSubst₁] at HstepRes₁
    apply pure_stepn.multi _ _ _ _ HstepRes₁
    apply pure_step.pure id; apply ctx𝕄.hole
    constructor; apply HwfBind₁.left; apply Hlc₁.right
    apply head.lets; apply HvalueBind₁
  . apply logic_rel_value.weakening
    apply Hsem_value; omega
