
import CollapsingTowers.TwoLevelBasic.Erasure
abbrev Subst :=
  List Expr

@[simp]
def multi_subst : Subst → Expr → Expr
  | [], e => e
  | v :: γ, e => subst (γ.length) v (multi_subst γ e)

@[simp]
def multi_lc : Subst → Prop
  | [] => true
  | v :: γ => lc v ∧ multi_lc γ

theorem multi_subst_lc : ∀ γ e, multi_lc γ → lc e → lc (multi_subst γ e) :=
  by
  intros γ e Hγ He
  induction γ
  case nil => apply He
  case cons IH =>
    rw [multi_subst]
    apply subst_lc_at; apply Hγ.left
    apply IH; apply Hγ.right

@[simp]
theorem multi_subst_app₁ : ∀ γ f arg, multi_subst γ (.app₁ f arg) = .app₁ (multi_subst γ f) (multi_subst γ arg) :=
  by
  intros γ f arg
  induction γ
  case nil => rfl
  case cons IH => simp [IH]

@[simp]
theorem multi_subst_lit : ∀ γ n, multi_subst γ (.lit n) = .lit n :=
  by
  intros γ n
  induction γ
  case nil => rfl
  case cons IH => simp [IH]

mutual
-- 𝓥⟦nat⟧ ≜ {(n, n) | n ∈ ℕ}
-- 𝓥⟦τ𝕒 → τ𝕓⟧ ≜ {(λ.e₀, λ.e₁) | ∀ (v₀, v₁) ∈ 𝓥⟦τ𝕒⟧. lc (λ.e₀) ∧ lc (λ.e₁) ∧ (e₀⟦0/v₀⟧, e₁⟦0/v₁⟧) ∈ 𝓔⟦τ𝕓⟧}
@[simp]
def sem_equiv_value : Expr → Expr → Ty → Prop
  | .lit n₀, .lit n₁, .nat => n₀ = n₁
  | .lam e₀, .lam e₁, (.arrow τ𝕒 τ𝕓 .pure) =>
    lc (.lam e₀) ∧
    lc (.lam e₁) ∧
    ∀ v₀ v₁,
      sem_equiv_value v₀ v₁ τ𝕒 →
      sem_equiv_expr (open_subst v₀ e₀) (open_subst v₁ e₁) τ𝕓
  | _, _, _ => false

-- 𝓔⟦τ⟧ ≜ {(e₀, e₁) | ∃v₀ v₁. e₀ ↦* v₀ ∧ e₁ ↦* v₁ ∧ (v₀, v₁) ∈ 𝓥⟦τ⟧}
@[simp]
def sem_equiv_expr (e₀ : Expr) (e₁ : Expr) (τ : Ty) : Prop :=
    ∃ v₀ v₁,
      pure_stepn e₀ v₀ ∧
      pure_stepn e₁ v₁ ∧
      sem_equiv_value v₀ v₁ τ
end

inductive sem_equiv_env : Subst → Subst → TEnv → Prop where
  | nil : sem_equiv_env [] [] []
  | cons :
    ∀ v₀ γ₀ v₁ γ₁ τ Γ,
      sem_equiv_value v₀ v₁ τ →
      sem_equiv_env γ₀ γ₁ Γ →
      sem_equiv_env (v₀ :: γ₀) (v₁ :: γ₁) ((τ, .stat) :: Γ)

-- Γ ⊧ e₀ ≈ e₁ : τ ≜ ∀ (γ₀, γ₁) ∈ 𝓖⟦Γ⟧. (γ₀(e₀), γ₁(e₁)) ∈ 𝓔⟦τ⟧
@[simp]
def sem_equiv_typing (Γ : TEnv) (e₀ : Expr) (e₁ : Expr) (τ : Ty) : Prop :=
  ∀ γ₀ γ₁,
    sem_equiv_env γ₀ γ₁ Γ →
    sem_equiv_expr (multi_subst γ₀ e₀) (multi_subst γ₁ e₁) τ

theorem sem_equiv_value_impl_value :
  ∀ v₀ v₁ τ,
    sem_equiv_value v₀ v₁ τ →
    value v₀ ∧
    value v₁ :=
  by
  intros v₀ v₁ τ Hsem_value
  cases τ
  case nat =>
    cases v₀ <;> cases v₁ <;> simp at Hsem_value
    constructor
    apply value.lit
    apply value.lit
  case arrow φ =>
    cases v₀ <;> cases v₁ <;> cases φ <;> simp at Hsem_value
    have ⟨Hlc₀, Hlc₁, _⟩ := Hsem_value
    constructor
    apply value.lam; apply Hlc₀
    apply value.lam; apply Hlc₁
  all_goals simp at Hsem_value

theorem sem_equiv_env_impl_multi_lc :
  ∀ γ₀ γ₁ Γ,
    sem_equiv_env γ₀ γ₁ Γ →
    multi_lc γ₀ ∧
    multi_lc γ₁ :=
  by
  intros γ₀ γ₁ Γ H
  induction H
  case nil => repeat constructor
  case cons Hsem_value _ IH =>
    constructor
    . constructor
      apply value_lc; apply And.left
      apply sem_equiv_value_impl_value
      apply Hsem_value; apply IH.left
    . constructor
      apply value_lc; apply And.right
      apply sem_equiv_value_impl_value
      apply Hsem_value; apply IH.right

theorem sem_equiv_value_arrow_iff_lam :
  ∀ f₀ f₁ τ𝕒 τ𝕓,
    sem_equiv_value f₀ f₁ (.arrow τ𝕒 τ𝕓 .pure) →
    ∃ e₀ e₁,
      f₀ = .lam e₀ ∧ f₁ = .lam e₁ :=
  by
  intros f₀ f₁ τ𝕒 τ𝕓 Hsem_value
  cases f₀ <;> cases f₁ <;> simp at Hsem_value
  simp

theorem sem_equiv_expr_stepn :
  ∀ e₀ e₁ r₀ r₁ τ,
    sem_equiv_expr r₀ r₁ τ →
    pure_stepn e₀ r₀ → pure_stepn e₁ r₁ →
    sem_equiv_expr e₀ e₁ τ :=
  by
  intros e₀ e₁ r₀ r₁ τ Hsem_expr Hstepr₀ Hstepr₁
  simp only [sem_equiv_expr] at *
  have ⟨v₀, v₁, Hstepv₀, Hstepv₁, Hsem_value⟩ := Hsem_expr
  exists v₀, v₁; constructor
  apply pure_stepn_trans; apply Hstepr₀ ; apply Hstepv₀; constructor
  apply pure_stepn_trans; apply Hstepr₁ ; apply Hstepv₁
  apply Hsem_value

-- Γ ⊢ e : τ → |Γ| ⊧ |e| ≈ |e| : |τ|
theorem fundamental :
  ∀ Γ 𝕊 e τ φ,
    typing Γ 𝕊 e τ φ →
    sem_equiv_typing (erase_env Γ) (erase e) (erase e) (erase_ty τ) :=
  by
  intros Γ 𝕊 e τ φ Hτ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ φ (H : typing Γ 𝕊 e τ φ) =>
          sem_equiv_typing (erase_env Γ) (erase e) (erase e) (erase_ty τ))
      (fun Γ e τ φ (H : typing_reification Γ e τ φ) =>
          sem_equiv_typing (erase_env Γ) (erase e) (erase e) (erase_ty τ))
  case fvar =>
    intros _ _ _ _ Hbinds _
    admit
  case lam =>
    intros _ _ _ _ _ _ _ HwellBinds Hclose IH
    admit
  case lift_lam =>
    intros _ _ _ _ _ _ _ IH
    apply IH
  case app₁ =>
    intros _ _ _ _ _ _ _ _ _ Hf Harg IHf IHarg
    intros γ₀ γ₁ semΓ
    simp only [sem_equiv_typing, sem_equiv_expr] at IHarg IHf
    have ⟨Hmulti_lc₀, Hmulti_lc₁⟩ := sem_equiv_env_impl_multi_lc _ _ _ semΓ
    have ⟨v₀, v₁, Hstepv₀, Hstepv₁, Hsem_value⟩ := IHarg γ₀ γ₁ semΓ
    have ⟨Hvalue₀, Hvalue₁⟩ := sem_equiv_value_impl_value _ _ _ Hsem_value
    have ⟨lam₀, lam₁, Hsteplam₀, Hsteplam₁, Hsem_value_lam⟩ := IHf γ₀ γ₁ semΓ
    have ⟨e₀, e₁, HEq₀, HEq₁⟩ := sem_equiv_value_arrow_iff_lam lam₀ lam₁ _ _ Hsem_value_lam
    rw [HEq₀, HEq₁, erase_ty, pure_empty, sem_equiv_value] at Hsem_value_lam
    have ⟨Hlc₀, Hlc₁, Hsem_value_lam⟩ := Hsem_value_lam
    apply sem_equiv_expr_stepn; apply Hsem_value_lam; apply Hsem_value
    . simp
      -- left step
      apply pure_stepn_trans
      apply pure_stepn_at𝔹 _ _ _ (ctx𝔹.appl₁ _ _) Hsteplam₀
      apply multi_subst_lc; apply Hmulti_lc₀
      apply erase_lc_at; apply typing_regular; apply Harg; rw [HEq₀]
      -- right step
      apply pure_stepn_trans
      apply pure_stepn_at𝔹 _ _ _ (ctx𝔹.appr₁ _ _) Hstepv₀
      apply value.lam; apply Hlc₀
      -- head step
      apply pure_stepn.multi; apply pure_stepn.refl
      apply pure_step.pure_step𝕄 id; apply ctx𝕄.hole
      constructor; apply Hlc₀; apply value_lc; apply Hvalue₀
      apply head𝕄.app₁; apply Hvalue₀
    . simp
      -- left step
      apply pure_stepn_trans
      apply pure_stepn_at𝔹 _ _ _ (ctx𝔹.appl₁ _ _) Hsteplam₁
      apply multi_subst_lc; apply Hmulti_lc₁
      apply erase_lc_at; apply typing_regular; apply Harg; rw [HEq₁]
      -- right step
      apply pure_stepn_trans
      apply pure_stepn_at𝔹 _ _ _ (ctx𝔹.appr₁ _ _) Hstepv₁
      apply value.lam; apply Hlc₁
      -- head step
      apply pure_stepn.multi; apply pure_stepn.refl
      apply pure_step.pure_step𝕄 id; apply ctx𝕄.hole
      constructor; apply Hlc₁; apply value_lc; apply Hvalue₁
      apply head𝕄.app₁; apply Hvalue₁
  case app₂ =>
    intros _ _ _ _ _ _ _ Hf Harg IHf IHarg
    intros γ₀ γ₁ semΓ
    simp only [sem_equiv_typing, sem_equiv_expr] at IHarg IHf
    have ⟨Hmulti_lc₀, Hmulti_lc₁⟩ := sem_equiv_env_impl_multi_lc _ _ _ semΓ
    have ⟨v₀, v₁, Hstepv₀, Hstepv₁, Hsem_value⟩ := IHarg γ₀ γ₁ semΓ
    have ⟨Hvalue₀, Hvalue₁⟩ := sem_equiv_value_impl_value _ _ _ Hsem_value
    have ⟨lam₀, lam₁, Hsteplam₀, Hsteplam₁, Hsem_value_lam⟩ := IHf γ₀ γ₁ semΓ
    have ⟨e₀, e₁, HEq₀, HEq₁⟩ := sem_equiv_value_arrow_iff_lam lam₀ lam₁ _ _ Hsem_value_lam
    rw [HEq₀, HEq₁, erase_ty, erase_ty, pure_empty, sem_equiv_value] at Hsem_value_lam
    have ⟨Hlc₀, Hlc₁, Hsem_value_lam⟩ := Hsem_value_lam
    apply sem_equiv_expr_stepn; apply Hsem_value_lam; apply Hsem_value
    . simp
      -- left step
      apply pure_stepn_trans
      apply pure_stepn_at𝔹 _ _ _ (ctx𝔹.appl₁ _ _) Hsteplam₀
      apply multi_subst_lc; apply Hmulti_lc₀
      apply erase_lc_at; apply typing_regular; apply Harg; rw [HEq₀]
      -- right step
      apply pure_stepn_trans
      apply pure_stepn_at𝔹 _ _ _ (ctx𝔹.appr₁ _ _) Hstepv₀
      apply value.lam; apply Hlc₀
      -- head step
      apply pure_stepn.multi; apply pure_stepn.refl
      apply pure_step.pure_step𝕄 id; apply ctx𝕄.hole
      constructor; apply Hlc₀; apply value_lc; apply Hvalue₀
      apply head𝕄.app₁; apply Hvalue₀
    . simp
      -- left step
      apply pure_stepn_trans
      apply pure_stepn_at𝔹 _ _ _ (ctx𝔹.appl₁ _ _) Hsteplam₁
      apply multi_subst_lc; apply Hmulti_lc₁
      apply erase_lc_at; apply typing_regular; apply Harg; rw [HEq₁]
      -- right step
      apply pure_stepn_trans
      apply pure_stepn_at𝔹 _ _ _ (ctx𝔹.appr₁ _ _) Hstepv₁
      apply value.lam; apply Hlc₁
      -- head step
      apply pure_stepn.multi; apply pure_stepn.refl
      apply pure_step.pure_step𝕄 id; apply ctx𝕄.hole
      constructor; apply Hlc₁; apply value_lc; apply Hvalue₁
      apply head𝕄.app₁; apply Hvalue₁
  case lit =>
    intros _ _ n
    intros γ₀ γ₁ semΓ
    simp only [sem_equiv_expr]
    exists .lit n, .lit n
    simp; apply pure_stepn.refl
  case lift_lit =>
    intros _ _ _ _ IH
    apply IH
  case code_fragment =>
    intros _ x _ Hbinds HwellBinds
    admit
  case code_rep =>
    intros _ _ _ _ IH
    apply IH
  case reflect =>
    intros _ _ _ _ IH
    apply IH
  case lam𝕔 =>
    intros _ _ _ _ _ _ _ Hclose IH
    admit
  case lets =>
    intros _ _ _ _ _ _ _ _ _ _ _ Hclose IHb IHe
    admit
  case let𝕔 =>
    intros _ _ _ _ _ _ _ _ HwellBinds Hclose IHb IHe
    admit
  case run =>
    intros _ _ _ _ _ _ IH
    apply IH
  case pure =>
    intros _ _ _ _ IH
    apply IH
  case reify =>
    intros _ _ _ _ _ IH
    apply IH
  apply Hτ
