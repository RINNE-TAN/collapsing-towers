import CollapsingTowers.TwoLevelRec.OperationalSemantics.Refine

-- e₁⇓ ≜ ∃ v, e ⇝* v
@[simp]
def termination (e : Expr) : Prop :=
  ∃ v, value v ∧ e ⇝* v

lemma termination.under_stepn :
  ∀ e₀ e₁,
    (e₀ ⇝* e₁) →
    (termination e₀ ↔ termination e₁) :=
  by
  intros e₀ e₁ Hstepl
  constructor
  . intro Htermination
    have ⟨v, Hvalue, Hstepr⟩ := Htermination
    exists v; constructor
    . apply Hvalue
    . have ⟨r, Hstepl, Hstepr⟩ := stepn.church_rosser _ _ _ Hstepl Hstepr
      have HEq := stepn.value_impl_termination _ _ Hvalue Hstepr
      rw [HEq]
      apply Hstepl
  . intro Htermination
    have ⟨v, Hvalue, Hstepr⟩ := Htermination
    exists v; constructor
    . apply Hvalue
    . apply stepn.trans _ _ _ Hstepl Hstepr
