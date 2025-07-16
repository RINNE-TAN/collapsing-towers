
import CollapsingTowers.TwoLevelBasic.SemTyping
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
  intros γ₀ γ₁ HsemΓ
  simp only [sem_equiv_expr]
  exists multi_subst γ₀ (.fvar x), multi_subst γ₁ (.fvar x)
  constructor; apply pure_stepn.refl
  constructor; apply pure_stepn.refl
  apply sem_equiv_env_impl_sem_equiv_value
  apply HsemΓ; apply Hbinds

-- x ↦ τ𝕒, Γ ⊧ e₀⟦0 ↦ x⟧ ≈ e₁⟦0 ↦ x⟧ : τ𝕓
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
  intros γ₀ γ₁ HsemΓ
  have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := sem_equiv_env_impl_multi_wf _ _ _ HsemΓ
  have ⟨HEq₀, HEq₁⟩ := sem_equiv_env_impl_length_eq _ _ _ HsemΓ
  simp only [multi_subst_lam, sem_equiv_expr]
  exists .lam (multi_subst γ₀ e₀),.lam (multi_subst γ₁ e₁)
  constructor; apply pure_stepn.refl
  constructor; apply pure_stepn.refl
  simp only [pure_empty, sem_equiv_value]
  constructor; rw [← multi_subst_lam]; constructor
  . apply multi_subst_lc_at; apply Hmulti_wf₀; apply Hlc₀
  . apply multi_subst_closed; apply Hmulti_wf₀; rw [HEq₀]; apply Hclosed₀
  constructor; rw [← multi_subst_lam]; constructor
  . apply multi_subst_lc_at; apply Hmulti_wf₁; apply Hlc₁
  . apply multi_subst_closed; apply Hmulti_wf₁; rw [HEq₁]; apply Hclosed₁
  intros v₀ v₁ Hsem_value
  have ⟨Hwf₀, Hwf₁⟩ := sem_equiv_value_impl_wf _ _ _ Hsem_value
  simp only [sem_equiv_typing] at Hsem
  rw [open_subst, ← subst_intro γ₀.length (multi_subst γ₀ e₀)]
  rw [open_subst, ← subst_intro γ₁.length (multi_subst γ₁ e₁)]
  rw [← multi_subst_open₀_comm, multi_subst_comm, ← multi_subst, HEq₀]
  rw [← multi_subst_open₀_comm, multi_subst_comm, ← multi_subst, HEq₁]
  apply Hsem; apply sem_equiv_env.cons; apply Hsem_value; apply HsemΓ
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
  intros γ₀ γ₁ HsemΓ
  simp only [sem_equiv_typing, sem_equiv_expr] at Hf Harg
  have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := sem_equiv_env_impl_multi_wf _ _ _ HsemΓ
  have ⟨v₀, v₁, Hstepv₀, Hstepv₁, Hsem_value⟩ := Harg γ₀ γ₁ HsemΓ
  have ⟨Hvalue₀, Hvalue₁⟩ := sem_equiv_value_impl_value _ _ _ Hsem_value
  have ⟨lam₀, lam₁, Hsteplam₀, Hsteplam₁, Hsem_value_lam⟩ := Hf γ₀ γ₁ HsemΓ
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

-- Γ ⊧ b₀ ≈ b₁ : τ𝕒
-- x ↦ τ𝕒, Γ ⊧ e₀⟦0 ↦ x⟧ ≈ e₁⟦0 ↦ x⟧ : τ𝕓
-- ——————————————————————————————
-- Γ ⊧ lets b₀ e₀ ≈ lets b₁ e₁ : τ𝕓
theorem compatibility_lets :
  ∀ Γ b₀ b₁ e₀ e₁ τ𝕒 τ𝕓,
    lc (.lets b₀ e₀) →
    lc (.lets b₁ e₁) →
    closed_at (.lets b₀ e₀) Γ.length →
    closed_at (.lets b₁ e₁) Γ.length →
    sem_equiv_typing Γ b₀ b₁ τ𝕒 →
    sem_equiv_typing ((τ𝕒, .stat) :: Γ) (open₀ Γ.length e₀) (open₀ Γ.length e₁) τ𝕓 →
    sem_equiv_typing Γ (.lets b₀ e₀) (.lets b₁ e₁) τ𝕓 :=
  by
  intros Γ b₀ b₁ e₀ e₁ τ𝕒 τ𝕓 Hlc₀ Hlc₁ Hclosed₀ Hclosed₁ Hb He
  intros γ₀ γ₁ HsemΓ
  simp only [sem_equiv_typing, sem_equiv_expr] at Hb
  have ⟨Hmulti_wf₀, Hmulti_wf₁⟩ := sem_equiv_env_impl_multi_wf _ _ _ HsemΓ
  have ⟨HEq₀, HEq₁⟩ := sem_equiv_env_impl_length_eq _ _ _ HsemΓ
  have ⟨v₀, v₁, Hstepv₀, Hstepv₁, Hsem_value⟩ := Hb γ₀ γ₁ HsemΓ
  have ⟨Hvalue₀, Hvalue₁⟩ := sem_equiv_value_impl_value _ _ _ Hsem_value
  have ⟨Hwf₀, Hwf₁⟩ := sem_equiv_value_impl_wf _ _ _ Hsem_value
  apply sem_equiv_expr_stepn; apply He
  apply sem_equiv_env.cons; apply Hsem_value; apply HsemΓ
  . simp
    -- left step
    apply pure_stepn_trans
    apply pure_stepn_at𝔹 _ _ _ (ctx𝔹.lets _ _) Hstepv₀
    apply multi_subst_lc_at; apply Hmulti_wf₀; apply Hlc₀.right
    -- head step
    apply pure_stepn.multi; apply pure_stepn.refl
    rw [← multi_subst_comm, multi_subst_open₀_comm, HEq₀, subst_intro, ← open_subst]
    apply pure_step.pure_step𝕄 id; apply ctx𝕄.hole
    constructor; apply value_lc; apply Hvalue₀
    apply multi_subst_lc_at; apply Hmulti_wf₀; apply Hlc₀.right
    apply head𝕄.lets; apply Hvalue₀
    apply closed_inc; apply multi_subst_closed
    apply Hmulti_wf₀; rw [HEq₀]; apply Hclosed₀.right
    omega; omega; apply Hmulti_wf₀
    omega; apply Hwf₀.right; apply Hmulti_wf₀
  . simp
    -- left step
    apply pure_stepn_trans
    apply pure_stepn_at𝔹 _ _ _ (ctx𝔹.lets _ _) Hstepv₁
    apply multi_subst_lc_at; apply Hmulti_wf₁; apply Hlc₁.right
    -- head step
    apply pure_stepn.multi; apply pure_stepn.refl
    rw [← multi_subst_comm, multi_subst_open₀_comm, HEq₁, subst_intro, ← open_subst]
    apply pure_step.pure_step𝕄 id; apply ctx𝕄.hole
    constructor; apply value_lc; apply Hvalue₁
    apply multi_subst_lc_at; apply Hmulti_wf₁; apply Hlc₁.right
    apply head𝕄.lets; apply Hvalue₁
    apply closed_inc; apply multi_subst_closed
    apply Hmulti_wf₁; rw [HEq₁]; apply Hclosed₁.right
    omega; omega; apply Hmulti_wf₁
    omega; apply Hwf₁.right; apply Hmulti_wf₁

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
    intros _ _ _ _ _ _ _ _ Hb He _ Hclose IHb IHe
    apply compatibility_lets
    constructor
    . apply erase_lc_at; apply typing_regular; apply Hb
    . apply erase_lc_at; apply (open_lc _ _ _).mp;apply typing_regular; apply He
    constructor
    . apply erase_lc_at; apply typing_regular; apply Hb
    . apply erase_lc_at; apply (open_lc _ _ _).mp;apply typing_regular; apply He
    constructor
    . rw [← length_erase_env]; apply erase_closed_at; apply typing_closed; apply Hb
    . rw [← length_erase_env]; apply erase_closed_at; apply Hclose
    constructor
    . rw [← length_erase_env]; apply erase_closed_at; apply typing_closed; apply Hb
    . rw [← length_erase_env]; apply erase_closed_at; apply Hclose
    apply IHb
    rw [← erase_env, ← length_erase_env, ← erase_open₀_comm]
    apply IHe
  case let𝕔 =>
    intros _ _ _ _ _ _ Hb He _ Hclose IHb IHe
    apply compatibility_lets
    constructor
    . apply erase_lc_at; apply typing_regular; apply Hb
    . apply erase_lc_at; apply (open_lc _ _ _).mp;apply typing_reification_regular; apply He
    constructor
    . apply erase_lc_at; apply typing_regular; apply Hb
    . apply erase_lc_at; apply (open_lc _ _ _).mp;apply typing_reification_regular; apply He
    constructor
    . rw [← length_erase_env]; apply erase_closed_at; apply typing_closed; apply Hb
    . rw [← length_erase_env]; apply erase_closed_at; apply Hclose
    constructor
    . rw [← length_erase_env]; apply erase_closed_at; apply typing_closed; apply Hb
    . rw [← length_erase_env]; apply erase_closed_at; apply Hclose
    apply IHb
    rw [← erase_env, ← length_erase_env, ← erase_open₀_comm]
    apply IHe
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

theorem fundamental_reification :
  ∀ Γ e τ φ,
    typing_reification Γ e τ φ →
    sem_equiv_typing (erase_env Γ) (erase e) (erase e) (erase_ty τ) :=
  by
  intros Γ e τ φ Hτ
  cases Hτ
  all_goals
  next Hτ =>
    apply fundamental _ _ _ _ _ Hτ
