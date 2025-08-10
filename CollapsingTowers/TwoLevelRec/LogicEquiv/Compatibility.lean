import CollapsingTowers.TwoLevelRec.LogicEquiv.LogicRelation

-- Γ ⊧ x ≤𝑙𝑜𝑔 x : Γ(x)
lemma compatibility.fvar :
  ∀ Γ x τ,
    binds x (τ, 𝟙) Γ →
    wbt 𝟙 τ →
    logic_rel_typing Γ (.fvar x) (.fvar x) τ :=
  by
  intros Γ x τ Hbinds Hwbt
  constructor; apply typing.fvar; apply Hbinds; apply Hwbt
  constructor; apply typing.fvar; apply Hbinds; apply Hwbt
  intros k γ₀ γ₁ HsemΓ
  simp only [logic_rel_expr]
  intros z Hindexz v₀ Hvalue₀ Hstep₀
  exists multi_subst γ₁ (.fvar x)
  constructor
  . apply pure_stepn.refl
  . have Hsem_value := logic_rel_env.binds_logic_rel_value _ _ _ _ _ _ HsemΓ Hbinds
    have ⟨Hvalue₀, Hvalue₁⟩ := logic_rel_value.syntactic.value _ _ _ _ Hsem_value
    have ⟨HEqv, Hz⟩ := pure_stepn_indexed.value_impl_termination _ _ _ Hvalue₀ Hstep₀
    rw [← HEqv, Hz]; apply Hsem_value

-- Γ ⊧ n ≤𝑙𝑜𝑔 n : ℕ
lemma compatibility.lit :
  ∀ Γ n, logic_rel_typing Γ (.lit n) (.lit n) .nat :=
  by
  intros _ n
  constructor; apply typing.lit
  constructor; apply typing.lit
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
-- ——————————————————————————————
-- Γ ⊧ λx.e₀ ≤𝑙𝑜𝑔 λx.e₁ : τ𝕒 → τ𝕓
lemma compatibility.lam :
  ∀ Γ e₀ e₁ τ𝕒 τ𝕓,
    wbt 𝟙 τ𝕒 →
    closed_at e₀ Γ.length →
    closed_at e₁ Γ.length →
    logic_rel_typing ((τ𝕒, 𝟙) :: Γ) ({0 ↦ Γ.length} e₀) ({0 ↦ Γ.length} e₁) τ𝕓 →
    logic_rel_typing Γ (.lam e₀) (.lam e₁) (.arrow τ𝕒 τ𝕓 ∅) :=
  by
  intros Γ e₀ e₁ τ𝕒 τ𝕓 Hwbt Hclosed₀ Hclosed₁ He
  have ⟨Hτ₀, Hτ₁, He⟩ := He
  have Hτ₀ : typing Γ 𝟙 (.lam e₀) (.arrow τ𝕒 τ𝕓 ∅) ∅ := by apply typing.lam; apply Hτ₀; apply Hwbt; apply Hclosed₀
  have Hτ₁ : typing Γ 𝟙 (.lam e₁) (.arrow τ𝕒 τ𝕓 ∅) ∅ := by apply typing.lam; apply Hτ₁; apply Hwbt; apply Hclosed₁
  constructor; apply Hτ₀
  constructor; apply Hτ₁
  intros k γ₀ γ₁ HsemΓ
  have ⟨Hτ₀, Hτ₁⟩ := logic_rel_env.subst.typing _ _ _ _ _ _ _ Hτ₀ Hτ₁ HsemΓ
  have ⟨Hlc₀, Hclosed₀⟩ := typing.wf _ _ _ _ _ Hτ₀
  have ⟨Hlc₁, Hclosed₁⟩ := typing.wf _ _ _ _ _ Hτ₁
  simp at Hτ₀ Hτ₁ Hlc₀ Hlc₁ Hclosed₀ Hclosed₁
  have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := logic_rel_env.multi_wf _ _ _ _ HsemΓ
  have ⟨HEq₀, HEq₁⟩ := logic_rel_env.length _ _ _ _ HsemΓ
  rw [logic_rel_expr]
  intros z Hindexz v₀ Hvalue₀ Hstep₀
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
  constructor; apply Hτ₀
  constructor; apply Hτ₁
  intros k Hindexk argv₀ argv₁ Hsem_value_arg
  have ⟨HvalueArg₀, HvalueArg₁⟩ := logic_rel_value.syntactic.value _ _ _ _ Hsem_value_arg
  have ⟨HτArg₀, HτArg₁⟩ := logic_rel_value.syntactic.typing _ _ _ _ Hsem_value_arg
  have ⟨HlcArg₀, HclosedArg₀⟩ := typing.wf _ _ _ _ _ HτArg₀
  have ⟨HlcArg₁, HclosedArg₁⟩ := typing.wf _ _ _ _ _ HτArg₁
  rw [logic_rel_expr]
  intros j Hindexj v₀ Hvalue₀ Hstep₀
  --
  --
  -- λx.γ₀(e₀) @ argv₀ ⇾ ⟦j⟧ v₀
  -- —————————————————————————————
  -- j = i + 1
  -- (x ↦ argv₀, γ₀)(e₀) ⇾ ⟦i⟧ v₀
  have ⟨i, HEqj, Hstep₀⟩ := pure_stepn_indexed.refine.lam _ _ _ _ (value.lam _ Hlc₀) HvalueArg₀ Hvalue₀ Hstep₀
  --
  --
  -- (x ↦ argv₀, γ₀)(e₀) ⇾ ⟦i⟧ v₀
  -- ((x ↦ argv₀, γ₀)(e₀), (x ↦ argv₁, γ₁)(e₁)) ∈ 𝓔⟦τ𝕓⟧ₖ
  -- ——————————————————————————————————————————————————————
  -- (x ↦ argv₁, γ₁)(e₁) ⇾* v₁
  -- (v₀, v₁) ∈ 𝓥⟦τ𝕓⟧ₖ₋ᵢ
  have HEqSubst₀ : opening 0 argv₀ (multi_subst γ₀ e₀) = multi_subst (argv₀ :: γ₀) ({0 ↦ Γ.length} e₀) :=
    by
    rw [multi_subst, ← comm.multi_subst_subst _ _ _ _ _ _ Hmulti_wf₀]
    rw [comm.multi_subst_opening _ _ _ _ _ Hmulti_wf₀]
    rw [HEq₀, intros.subst]
    apply closed.inc; apply Hclosed₀; simp
    omega; omega; apply HclosedArg₀
  rw [HEqSubst₀] at Hstep₀
  have HsemΓ : logic_rel_env k (argv₀ :: γ₀) (argv₁ :: γ₁) ((τ𝕒, 𝟙) :: Γ) :=
    by
    apply logic_rel_env.cons; apply Hsem_value_arg
    apply logic_rel_env.antimono; apply HsemΓ; omega
  have Hsem_expr := He _ _ _ HsemΓ
  rw [logic_rel_expr] at Hsem_expr
  have ⟨v₁, Hstep₁, Hsem_value⟩ := Hsem_expr i (by omega) _ Hvalue₀ Hstep₀
  --
  --
  -- (x ↦ argv₁, γ₁)(e₁) ⇾* v₁
  -- ——————————————————————————
  -- λx.γ₁(e₁) @ argv₁ ⇾* v₁
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
    apply pure_stepn.multi _ _ _ _ Hstep₁
    apply pure_step.pure id; apply ctx𝕄.hole
    constructor; apply Hlc₁; apply lc.value; apply HvalueArg₁
    apply head.app₁; apply HvalueArg₁
  . apply logic_rel_value.antimono
    apply Hsem_value; omega
