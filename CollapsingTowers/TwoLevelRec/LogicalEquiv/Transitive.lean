import CollapsingTowers.TwoLevelRec.LogicalEquiv.Fundamental
mutual
-- (v₀, v₁) ∈ 𝓥⟦τ⟧ₖ
-- ∀ k. (v₁, v₂) ∈ 𝓥⟦τ⟧ₖ
-- ————————————————————
-- (v₀, v₂) ∈ 𝓥⟦τ⟧ₖ
lemma log_rel_value.trans :
  ∀ k v₀ v₁ v₂ τ,
    log_rel_value k v₀ v₁ τ →
    (∀ k, log_rel_value k v₁ v₂ τ) →
    log_rel_value k v₀ v₂ τ :=
  by
  intros k v₀ v₁ v₂ τ Hsem_value₀ Hsem_value₁
  cases τ
  case nat =>
    cases v₀ <;> try simp at Hsem_value₀
    cases v₁ <;> try simp at Hsem_value₀
    cases v₂ <;> try simp at Hsem_value₁
    simp; omega
  case arrow τ𝕒 τ𝕓 φ =>
    cases v₀ <;> try simp at Hsem_value₀
    case lam e₀ =>
    cases v₁ <;> try simp at Hsem_value₀
    case lam e₁ =>
    cases v₂ <;> try simp at Hsem_value₁
    case lam e₂ =>
    cases φ <;> simp only [log_rel_value] at Hsem_value₀ Hsem_value₁ <;> try contradiction
    simp only [log_rel_value]
    have ⟨Hτ₀, Hτ₁, Hsem_expr₀⟩ := Hsem_value₀
    have ⟨Hτ₁, Hτ₂, _⟩ := Hsem_value₁ 0
    constructor; apply Hτ₀
    constructor; apply Hτ₂
    intros j Hindexj argv₀ argv₁ Hsem_value_arg₀
    have ⟨HvalueArg₀, HvalueArg₁⟩ := log_rel_value.syntactic.value _ _ _ _ Hsem_value_arg₀
    have ⟨HτArg₀, HτArg₁⟩ := log_rel_value.syntactic.typing _ _ _ _ Hsem_value_arg₀
    apply log_rel_expr.trans; apply Hsem_expr₀
    apply Hindexj; apply Hsem_value_arg₀
    intros k
    cases k
    case zero => simp
    case succ k =>
      have ⟨Hτ₁, Hτ₂, Hsem_expr₁⟩ := Hsem_value₁ (k + 1)
      apply Hsem_expr₁; omega
      have ⟨_, _, Hsem_expr_argv₁⟩ := typing.fundamental _ _ _ HτArg₁
      simp only [log_rel_expr] at Hsem_expr_argv₁
      have ⟨argv₂, Hstep, Hsem_value_arg₁⟩ := Hsem_expr_argv₁ (k + 1) [] [] (log_rel_env.nil _) 0 (by omega) _ HvalueArg₁ (stepn_indexed.refl _)
      rw [← stepn.value_impl_termination _ _ HvalueArg₁ Hstep] at Hsem_value_arg₁
      apply Hsem_value_arg₁
  case fragment => simp at Hsem_value₀
  case rep => simp at Hsem_value₀

termination_by k _ _ _ τ => (τ, k)
decreasing_by next HEqτ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rw [HEqτ]; apply Prod.Lex.left; simp; omega

-- (e₀, e₁) ∈ 𝓔⟦τ⟧ₖ
-- ∀ k. (e₁, e₂) ∈ 𝓔⟦τ⟧ₖ
-- ————————————————————
-- (e₀, e₂) ∈ 𝓔⟦τ⟧ₖ
lemma log_rel_expr.trans :
  ∀ k e₀ e₁ e₂ τ,
    log_rel_expr k e₀ e₁ τ →
    (∀ k, log_rel_expr k e₁ e₂ τ) →
    log_rel_expr k e₀ e₂ τ :=
  by
  intros k e₀ e₁ e₂ τ Hsem_expr₀ Hsem_expr₁
  cases k
  case zero => simp
  case succ k =>
    simp only [log_rel_expr] at Hsem_expr₀ Hsem_expr₁
    simp only [log_rel_expr]
    intros i₀ Hindexi₀ v₀ Hvalue₀ Hstep₀
    have ⟨v₁, Hstep₁, Hsem_value₀⟩ := Hsem_expr₀ _ Hindexi₀ _ Hvalue₀ Hstep₀
    have ⟨Hvalue₀, Hvalue₁⟩ := log_rel_value.syntactic.value _ _ _ _ Hsem_value₀
    have ⟨i₁, Hstep₁⟩ := stepn_impl_stepn_indexed _ _ Hstep₁
    have ⟨v₂, Hstep₂, Hsem_value₁⟩ := Hsem_expr₁ (i₁ + 1) i₁ (by omega) _ Hvalue₁ Hstep₁
    have ⟨Hvalue₁, Hvalue₂⟩ := log_rel_value.syntactic.value _ _ _ _ Hsem_value₁
    exists v₂
    constructor; apply Hstep₂
    apply log_rel_value.trans; apply Hsem_value₀
    intros k
    have ⟨v₃, Hstep₃, Hsem_value₂⟩ := Hsem_expr₁ (k + i₁ + 1) i₁ (by omega) _ Hvalue₁ Hstep₁
    have ⟨Hvalue₁, Hvalue₃⟩ := log_rel_value.syntactic.value _ _ _ _ Hsem_value₂
    rw [stepn.unique_normal_forms _ _ _ Hstep₂ Hstep₃ Hvalue₂ Hvalue₃]
    apply log_rel_value.antimono
    apply Hsem_value₂; omega

termination_by k _ _ _ τ => (τ, k + 1)
decreasing_by apply Prod.Lex.right; omega
end
