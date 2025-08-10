import CollapsingTowers.TwoLevelRec.LogicalEquiv.Fundamental

lemma log_rel_value.refl.zero_case :
  ∀ v₀ v₁ τ,
    log_rel_value 0 v₀ v₁ τ →
    log_rel_value 0 v₀ v₀ τ ∧
    log_rel_value 0 v₁ v₁ τ :=
  by
  intros v₀ v₁ τ Hsem_value
  cases τ
  case nat =>
    cases v₀ <;> cases v₁ <;> simp at Hsem_value
    constructor; simp; simp
  case arrow φ =>
    cases v₀ <;> cases v₁ <;> cases φ <;> simp at Hsem_value
    constructor
    . rw [log_rel_value]
      constructor; apply Hsem_value.left
      constructor; apply Hsem_value.left
      intro z Hindexz argv₀ argv₁ Hsem_value_arg
      rw [log_rel_expr]
      intro j Hindexj; omega
    . rw [log_rel_value]
      constructor; apply Hsem_value.right
      constructor; apply Hsem_value.right
      intro z Hindexz argv₀ argv₁ Hsem_value_arg
      rw [log_rel_expr]
      intro j Hindexj; omega
  all_goals simp at Hsem_value

lemma log_rel_value.refl :
  ∀ k v₀ v₁ τ,
    log_rel_value k ‖v₀‖ ‖v₁‖ ‖τ‖𝜏 →
    log_rel_value k ‖v₀‖ ‖v₀‖ ‖τ‖𝜏 ∧
    log_rel_value k ‖v₁‖ ‖v₁‖ ‖τ‖𝜏 :=
  by
  intros k v₀ v₁ τ Hsem_value
  cases k
  case zero =>
    apply log_rel_value.refl.zero_case
    apply Hsem_value
  case succ k =>
    have ⟨Hvalue₀, Hvalue₁⟩ := log_rel_value.syntactic.value _ _ _ _ Hsem_value
    have ⟨Hτ₀, Hτ₁⟩ := log_rel_value.syntactic.typing _ _ _ _ Hsem_value
    have ⟨_, _, H₀⟩ := typing.fundamental [] _ _ _ _ Hτ₀
    have ⟨_, _, H₁⟩ := typing.fundamental [] _ _ _ _ Hτ₁
    have Hsem_expr₀ := H₀ (k + 1) _ _ (log_rel_env.nil _)
    have Hsem_expr₁ := H₁ (k + 1) _ _ (log_rel_env.nil _)
    rw [log_rel_expr] at Hsem_expr₀ Hsem_expr₁
    have ⟨r₀, Hstepr₀, Hsem_value₀⟩ := Hsem_expr₀ 0 (by omega) _ Hvalue₀ (pure_stepn_indexed.refl _)
    have ⟨r₁, Hstepr₁, Hsem_value₁⟩ := Hsem_expr₁ 0 (by omega) _ Hvalue₁ (pure_stepn_indexed.refl _)
    have HEqv₀ := pure_stepn.value_impl_termination _ _ Hvalue₀ Hstepr₀
    have HEqv₁ := pure_stepn.value_impl_termination _ _ Hvalue₁ Hstepr₁
    rw [← HEqv₀] at Hsem_value₀
    rw [← HEqv₁] at Hsem_value₁
    constructor; apply Hsem_value₀; apply Hsem_value₁
