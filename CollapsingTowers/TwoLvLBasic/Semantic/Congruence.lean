import CollapsingTowers.TwoLvLBasic.Semantic.SmallStep

lemma pure_step.congruence_under_ctx𝔹 : ∀ B e₀ e₁, ctx𝔹 B → (e₀ ⇾ e₁) → (B⟦e₀⟧ ⇾ B⟦e₁⟧) :=
  by
  intros B e₀ e₁ HB Hstep
  cases Hstep
  case pure M _ _ HM Hlc Hhead =>
    rw [ctx_comp B M]
    apply pure_step.pure
    apply ctx𝕄.cons𝔹; apply HB; apply HM
    apply Hlc; apply Hhead

lemma pure_step.congruence_under_ctx𝔼 : ∀ E e₀ e₁, ctx𝔼 E → (e₀ ⇾ e₁) → (E⟦e₀⟧ ⇾ E⟦e₁⟧) :=
  by
  intros E e₀ e₁ HE Hstep
  induction HE
  case hole => apply Hstep
  case cons𝔹 HB _ IH =>
    simp; apply congruence_under_ctx𝔹
    apply HB; apply IH

lemma pure_stepn.congruence_under_ctx𝔹 : ∀ B e₀ e₁, ctx𝔹 B → (e₀ ⇾* e₁) → (B⟦e₀⟧ ⇾* B⟦e₁⟧) :=
  by
  intros B e₀ e₁ HB Hstepn
  induction Hstepn
  case refl => apply pure_stepn.refl
  case multi H _ IH =>
    apply pure_stepn.multi
    apply pure_step.congruence_under_ctx𝔹
    apply HB; apply H; apply IH

lemma pure_stepn.congruence_under_ctx𝔼 : ∀ E e₀ e₁, ctx𝔼 E → (e₀ ⇾* e₁) → (E⟦e₀⟧ ⇾* E⟦e₁⟧) :=
  by
  intros E e₀ e₁ HE Hstepn
  induction Hstepn
  case refl => apply pure_stepn.refl
  case multi H _ IH =>
    apply pure_stepn.multi
    apply pure_step.congruence_under_ctx𝔼
    apply HE; apply H; apply IH
