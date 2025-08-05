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
  intros j Hindex v₀ Hstep₀ Hvalue₀
  exists multi_subst γ₁ (.fvar x)
  constructor
  . apply pure_stepn.refl
  . have Hsem_value := logic_rel_env.binds_logic_rel_value _ _ _ _ _ _ HsemΓ Hbinds
    have ⟨Hvalue₀, Hvalue₁⟩ := logic_rel_value.syntactic_value _ _ _ _ Hsem_value
    have ⟨HEqv, Hj⟩ := pure_stepn_indexed.value_impl_termination _ _ _ Hvalue₀ Hstep₀
    rw [← HEqv, Hj]; apply Hsem_value
