
import CollapsingTowers.TwoLevelBasic.Erasure
mutual
-- 𝓥⟦nat⟧ ≜ {(n, n) | n ∈ ℕ}
-- 𝓥⟦τ𝕒 → τ𝕓⟧ ≜ {(λ.e₀, λ.e₁) | ∀ (v₀, v₁) ∈ 𝓥⟦τ𝕒⟧. wf (λ.e₀) ∧ wf (λ.e₁) ∧ (e₀⟦0 ↦ v₀⟧, e₁⟦0 ↦ v₁⟧) ∈ 𝓔⟦τ𝕓⟧}
@[simp]
def sem_equiv_value : Expr → Expr → Ty → Prop
  | .lit n₀, .lit n₁, .nat => n₀ = n₁
  | .lam e₀, .lam e₁, (.arrow τ𝕒 τ𝕓 .pure) =>
      wf (.lam e₀) ∧
      wf (.lam e₁) ∧
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
    have ⟨Hwf₀, Hwf₁, _⟩ := Hsem_value
    constructor
    apply value.lam; apply Hwf₀.left
    apply value.lam; apply Hwf₁.left
  all_goals simp at Hsem_value

theorem sem_equiv_value_impl_wf :
  ∀ v₀ v₁ τ,
    sem_equiv_value v₀ v₁ τ →
    wf v₀ ∧
    wf v₁ :=
  by
  intros v₀ v₁ τ Hsem_value
  cases τ
  case nat =>
    cases v₀ <;> cases v₁ <;> simp at Hsem_value
    repeat constructor
  case arrow φ =>
    cases v₀ <;> cases v₁ <;> cases φ <;> simp at Hsem_value
    have ⟨Hwf₀, Hwf₁, _⟩ := Hsem_value
    constructor
    apply Hwf₀; apply Hwf₁
  all_goals simp at Hsem_value

theorem sem_equiv_env_impl_multi_wf :
  ∀ γ₀ γ₁ Γ,
    sem_equiv_env γ₀ γ₁ Γ →
    multi_wf γ₀ ∧
    multi_wf γ₁ :=
  by
  intros γ₀ γ₁ Γ H
  induction H
  case nil => repeat constructor
  case cons Hsem_value _ IH =>
    constructor
    . constructor; apply And.left
      apply sem_equiv_value_impl_wf
      apply Hsem_value; apply IH.left
    . constructor; apply And.right
      apply sem_equiv_value_impl_wf
      apply Hsem_value; apply IH.right

theorem sem_equiv_env_impl_length_eq :
  ∀ γ₀ γ₁ Γ,
    sem_equiv_env γ₀ γ₁ Γ →
    γ₀.length = Γ.length ∧
    γ₁.length = Γ.length :=
  by
  intros γ₀ γ₁ Γ H
  induction H
  case nil => simp
  case cons IH =>
    constructor
    . simp; apply IH.left
    . simp; apply IH.right

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

-- Γ ⊧ x ≈ x : Γ(x)
theorem compatibility_fvar :
  ∀ Γ x τ,
    binds x (τ, .stat) Γ →
    sem_equiv_typing Γ (.fvar x) (.fvar x) τ :=
  by
  intros Γ x τ Hbinds
  intros γ₀ γ₁ semΓ
  simp only [sem_equiv_expr]
  exists multi_subst γ₀ (.fvar x), multi_subst γ₁ (.fvar x)
  constructor; apply pure_stepn.refl
  constructor; apply pure_stepn.refl
  induction semΓ
  case nil => nomatch Hbinds
  case cons v₀ γ₀ v₁ γ₁ τ Γ Hsem_value semΓ IH =>
    have ⟨Hwf₀, Hwf₁⟩ := sem_equiv_value_impl_wf _ _ _ Hsem_value
    have ⟨HEq₀, HEq₁⟩ := sem_equiv_env_impl_length_eq _ _ _ semΓ
    simp [HEq₀, HEq₁]
    by_cases HEqx : Γ.length = x
    . simp [if_pos HEqx]
      simp [if_pos HEqx] at Hbinds
      rw [← Hbinds, multi_subst_closed_id, multi_subst_closed_id]
      apply Hsem_value; apply Hwf₁.right; apply Hwf₀.right
    . simp [if_neg HEqx]
      simp [if_neg HEqx] at Hbinds
      apply IH; apply Hbinds

-- τ𝕒, Γ ⊧ e₀⟦0 ↦ 𝓛(Γ)⟧ ≈ e₁⟦0 ↦ 𝓛(Γ)⟧ : τ𝕓
-- —————————————————————————————————————————
-- Γ ⊧ λ.e₀ ≈ λ.e₁ : τ𝕒 → τ𝕓
theorem compatibility_lam :
  ∀ Γ e₀ e₁ τ𝕒 τ𝕓,
    lc (.lam e₀) →
    lc (.lam e₁) →
    closed_at (.lam e₀) Γ.length →
    closed_at (.lam e₁) Γ.length →
    sem_equiv_typing ((τ𝕒, .stat) :: Γ) (open₀ Γ.length e₀) (open₀ Γ.length e₁) τ𝕓 →
    sem_equiv_typing Γ (.lam e₀) (.lam e₁) (.arrow τ𝕒 τ𝕓 ∅) :=
  by
  intros Γ e₀ e₁ τ𝕒 τ𝕓 Hlc₀ Hlc₁ Hclosed₀ Hclosed₁ Hsem
  intros γ₀ γ₁ semΓ
  have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := sem_equiv_env_impl_multi_wf _ _ _ semΓ
  have ⟨HEq₀, HEq₁⟩ := sem_equiv_env_impl_length_eq _ _ _ semΓ
  simp only [multi_subst_lam, sem_equiv_expr]
  exists .lam (multi_subst γ₀ e₀),.lam (multi_subst γ₁ e₁)
  constructor; apply pure_stepn.refl
  constructor; apply pure_stepn.refl
  simp only [pure_empty, sem_equiv_value]
  constructor; rw [← multi_subst_lam]; constructor
  . apply multi_subst_lc; apply Hmulti_wf₀; apply Hlc₀
  . apply multi_subst_closed; apply Hmulti_wf₀; rw [HEq₀]; apply Hclosed₀
  constructor; rw [← multi_subst_lam]; constructor
  . apply multi_subst_lc; apply Hmulti_wf₁; apply Hlc₁
  . apply multi_subst_closed; apply Hmulti_wf₁; rw [HEq₁]; apply Hclosed₁
  intros v₀ v₁ Hsem_value
  have ⟨Hwf₀, Hwf₁⟩ := sem_equiv_value_impl_wf _ _ _ Hsem_value
  simp only [sem_equiv_typing] at Hsem
  rw [open_subst, ← subst_intro γ₀.length (multi_subst γ₀ e₀)]
  rw [open_subst, ← subst_intro γ₁.length (multi_subst γ₁ e₁)]
  rw [← multi_subst_opening_comm, multi_subst_comm, ← multi_subst, HEq₀]
  rw [← multi_subst_opening_comm, multi_subst_comm, ← multi_subst, HEq₁]
  apply Hsem; apply sem_equiv_env.cons; apply Hsem_value; apply semΓ
  omega; apply Hwf₁.right; apply Hmulti_wf₁; omega; apply Hmulti_wf₁
  omega; apply Hwf₀.right; apply Hmulti_wf₀; omega; apply Hmulti_wf₀
  . apply closed_inc; apply multi_subst_closed
    apply Hmulti_wf₁; rw [HEq₁]; apply Hclosed₁; omega
  . apply closed_inc; apply multi_subst_closed
    apply Hmulti_wf₀; rw [HEq₀]; apply Hclosed₀; omega

-- Γ ⊧ f₀ ≈ f₁ : τ𝕒 → τ𝕓
-- Γ ⊧ arg₀ ≈ arg₁ : τ𝕒
-- ——————————————————————————————
-- Γ ⊧ f₀ @ arg₀ ≈ f₁ @ arg₁ : τ𝕓
theorem compatibility_app :
  ∀ Γ f₀ f₁ arg₀ arg₁ τ𝕒 τ𝕓,
    sem_equiv_typing Γ f₀ f₁ (.arrow τ𝕒 τ𝕓 ∅) →
    sem_equiv_typing Γ arg₀ arg₁ τ𝕒 →
    sem_equiv_typing Γ (.app₁ f₀ arg₀) (.app₁ f₁ arg₁) τ𝕓 :=
  by
  intros Γ f₀ f₁ arg₀ arg₁ τ𝕒 τ𝕓 Hf Harg
  intros γ₀ γ₁ semΓ
  simp only [sem_equiv_typing, sem_equiv_expr] at Hf Harg
  have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := sem_equiv_env_impl_multi_wf _ _ _ semΓ
  have ⟨v₀, v₁, Hstepv₀, Hstepv₁, Hsem_value⟩ := Harg γ₀ γ₁ semΓ
  have ⟨Hvalue₀, Hvalue₁⟩ := sem_equiv_value_impl_value _ _ _ Hsem_value
  have ⟨lam₀, lam₁, Hsteplam₀, Hsteplam₁, Hsem_value_lam⟩ := Hf γ₀ γ₁ semΓ
  have ⟨e₀, e₁, HEq₀, HEq₁⟩ := sem_equiv_value_arrow_iff_lam lam₀ lam₁ _ _ Hsem_value_lam
  rw [HEq₀, HEq₁, pure_empty, sem_equiv_value] at Hsem_value_lam
  have ⟨Hwf₀, Hwf₁, Hsem_value_lam⟩ := Hsem_value_lam
  apply sem_equiv_expr_stepn; apply Hsem_value_lam; apply Hsem_value
  . simp
    -- left step
    apply pure_stepn_trans
    apply pure_stepn_at𝔹 _ _ _ (ctx𝔹.appl₁ _ _) Hsteplam₀
    apply pure_stepn_lc; apply Hstepv₀
    apply value_lc; apply Hvalue₀
    rw [HEq₀]
    -- right step
    apply pure_stepn_trans
    apply pure_stepn_at𝔹 _ _ _ (ctx𝔹.appr₁ _ _) Hstepv₀
    apply value.lam; apply Hwf₀.left
    -- head step
    apply pure_stepn.multi; apply pure_stepn.refl
    apply pure_step.pure_step𝕄 id; apply ctx𝕄.hole
    constructor; apply Hwf₀.left; apply value_lc; apply Hvalue₀
    apply head𝕄.app₁; apply Hvalue₀
  . simp
    -- left step
    apply pure_stepn_trans
    apply pure_stepn_at𝔹 _ _ _ (ctx𝔹.appl₁ _ _) Hsteplam₁
    apply pure_stepn_lc; apply Hstepv₁
    apply value_lc; apply Hvalue₁
    rw [HEq₁]
    -- right step
    apply pure_stepn_trans
    apply pure_stepn_at𝔹 _ _ _ (ctx𝔹.appr₁ _ _) Hstepv₁
    apply value.lam; apply Hwf₁.left
    -- head step
    apply pure_stepn.multi; apply pure_stepn.refl
    apply pure_step.pure_step𝕄 id; apply ctx𝕄.hole
    constructor; apply Hwf₁.left; apply value_lc; apply Hvalue₁
    apply head𝕄.app₁; apply Hvalue₁

-- Γ ⊢ e : τ
-- —————————————————————
-- |Γ| ⊧ |e| ≈ |e| : |τ|
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
    apply compatibility_fvar
    apply binds_erase_env; apply Hbinds
  case lam =>
    intros _ _ _ _ _ _ H _ Hclose IH
    apply compatibility_lam
    apply erase_lc_at; apply (open_lc _ _ _).mp; apply typing_regular; apply H
    apply erase_lc_at; apply (open_lc _ _ _).mp; apply typing_regular; apply H
    rw [← length_erase_env]; apply erase_closed_at; apply Hclose
    rw [← length_erase_env]; apply erase_closed_at; apply Hclose
    rw [← erase_env, ← length_erase_env, ← erase_open₀_comm]
    apply IH
  case lift_lam =>
    intros _ _ _ _ _ _ _ IH
    apply IH
  case app₁ =>
    intros _ _ _ _ _ _ _ _ _ Hf Harg IHf IHarg
    apply compatibility_app
    apply IHf; apply IHarg
  case app₂ =>
    intros _ _ _ _ _ _ _ _ _ IHf IHarg
    apply compatibility_app
    apply IHf; apply IHarg
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
    intros _ x _ Hbinds _
    apply compatibility_fvar; rw [erase_ty]
    apply binds_erase_env; apply Hbinds
  case code_rep =>
    intros _ _ _ _ IH
    apply IH
  case reflect =>
    intros _ _ _ _ IH
    apply IH
  case lam𝕔 =>
    intros _ _ _ _ _ H _ Hclose IH
    apply compatibility_lam
    apply erase_lc_at; apply (open_lc _ _ _).mp; apply typing_reification_regular; apply H
    apply erase_lc_at; apply (open_lc _ _ _).mp; apply typing_reification_regular; apply H
    rw [← length_erase_env]; apply erase_closed_at; apply Hclose
    rw [← length_erase_env]; apply erase_closed_at; apply Hclose
    rw [← erase_env, ← length_erase_env, ← erase_open₀_comm]
    apply IH
  case lets =>
    intros _ _ _ _ _ _ _ _ _ _ _ Hclose IHb IHe
    admit
  case let𝕔 =>
    intros _ _ _ _ _ _ _ _ _ Hclose IHb IHe
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
