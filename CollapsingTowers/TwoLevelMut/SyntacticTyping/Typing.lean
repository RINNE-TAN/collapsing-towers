import CollapsingTowers.TwoLevelMut.Syntax.Defs
import CollapsingTowers.TwoLevelMut.SyntacticTyping.Env
import CollapsingTowers.TwoLevelMut.OperationalSemantics.Defs
mutual
  inductive typing : Store → TEnv → Stage → Expr → Ty → REffects → MEffects → Prop where
    | fvar : ∀ σ Γ 𝕊 x τ,
      binds x (τ, 𝕊) Γ →
      wbt 𝕊 τ →
      typing σ Γ 𝕊 (.fvar x) τ ⊥ ∅
    | lam : ∀ σ Γ 𝕊 e τ𝕒 τ𝕓 φ ω,
      typing σ ((τ𝕒, 𝕊) :: Γ) 𝕊 ({0 ↦ Γ.length} e) τ𝕓 φ ω →
      wbt 𝕊 τ𝕒 →
      closed_at e Γ.length →
      typing σ Γ 𝕊 (.lam e) (.arrow τ𝕒 τ𝕓 φ ω) ⊥ ∅
    | lift_lam : ∀ σ Γ e τ𝕒 τ𝕓 φ₀ φ₁ ω₀ ω₁,
      typing σ Γ 𝟙 e (.arrow (.fragment τ𝕒) (.fragment τ𝕓) φ₀ ω₀) φ₁ ω₁ →
      stage_meffects 𝟚 ω₀ →
      typing σ Γ 𝟙 (.lift e) (.fragment (.arrow τ𝕒 τ𝕓 ⊥ ω₀)) ⊤ ω₁
    | app₁ : ∀ σ Γ 𝕊 f arg τ𝕒 τ𝕓 φ₀ φ₁ φ₂ ω₀ ω₁ ω₂,
      typing σ Γ 𝕊 f (.arrow τ𝕒 τ𝕓 φ₀ ω₀) φ₁ ω₁ →
      typing σ Γ 𝕊 arg τ𝕒 φ₂ ω₂ →
      typing σ Γ 𝕊 (.app₁ f arg) τ𝕓 (φ₀ ∪ φ₁ ∪ φ₂) (ω₀ ∪ ω₁ ∪ ω₂)
    | app₂ : ∀ σ Γ f arg τ𝕒 τ𝕓 φ₁ φ₂ ω₀ ω₁ ω₂,
      typing σ Γ 𝟙 f (.fragment (.arrow τ𝕒 τ𝕓 ⊥ ω₀)) φ₁ ω₁ →
      typing σ Γ 𝟙 arg (.fragment τ𝕒) φ₂ ω₂ →
      typing σ Γ 𝟙 (.app₂ f arg) (.fragment τ𝕓) ⊤ (ω₀ ∪ ω₁ ∪ ω₂)
    | lit : ∀ σ Γ 𝕊 n,
      typing σ Γ 𝕊 (.lit n) .nat ⊥ ∅
    | lift_lit : ∀ σ Γ n φ ω,
      typing σ Γ 𝟙 n .nat φ ω →
      typing σ Γ 𝟙 (.lift n) (.fragment .nat) ⊤ ω
    | code_fragment : ∀ σ Γ x τ,
      binds x (τ, 𝟚) Γ →
      wbt 𝟚 τ →
      typing σ Γ 𝟙 (.code (.fvar x)) (.fragment τ) ⊥ ∅
    | code_rep : ∀ σ Γ e τ ω,
      typing σ Γ 𝟚 e τ ⊥ ω →
      typing σ Γ 𝟙 (.code e) (.rep τ) ⊥ ω
    | reflect : ∀ σ Γ e τ ω,
      typing σ Γ 𝟚 e τ ⊥ ω →
      typing σ Γ 𝟙 (.reflect e) (.fragment τ) ⊤ ω
    | lam𝕔 : ∀ σ Γ e τ𝕒 τ𝕓 φ ω,
      -- Γ, x² ↦ τ𝕒 ⊢ᵣ e : <τ𝕓> ! ω
      -- wbt_meffects 𝟚 ω
      -- ——————————————————————————————
      -- Γ ⊢ lam𝕔 x.e : <τ𝕒 →ω τ𝕓> ! ∅
      typing_reification σ ((τ𝕒, 𝟚) :: Γ) ({0 ↦ Γ.length} e) (.rep τ𝕓) φ ω →
      wbt 𝟚 τ𝕒 →
      closed_at e Γ.length →
      stage_meffects 𝟚 ω →
      typing σ Γ 𝟙 (.lam𝕔 e) (.fragment (.arrow τ𝕒 τ𝕓 ⊥ ω)) ⊤ ∅
    | lets : ∀ σ Γ 𝕊 b e τ𝕒 τ𝕓 φ₀ φ₁ ω₀ ω₁,
      typing σ Γ 𝕊 b τ𝕒 φ₀ ω₀ →
      typing σ ((τ𝕒, 𝕊) :: Γ) 𝕊 ({0 ↦ Γ.length} e) τ𝕓 φ₁ ω₁ →
      wbt 𝕊 τ𝕒 →
      closed_at e Γ.length →
      typing σ Γ 𝕊 (.lets b e) τ𝕓 (φ₀ ∪ φ₁) (ω₀ ∪ ω₁)
    | lets𝕔 : ∀ σ Γ b e τ𝕒 τ𝕓 φ₁ ω₀ ω₁,
      typing σ Γ 𝟚 b τ𝕒 ⊥ ω₀ →
      typing_reification σ ((τ𝕒, 𝟚) :: Γ) ({0 ↦ Γ.length} e) (.rep τ𝕓) φ₁ ω₁ →
      wbt 𝟚 τ𝕒 →
      closed_at e Γ.length →
      typing σ Γ 𝟙 (.lets𝕔 b e) (.rep τ𝕓) ⊥ (ω₀ ∪ ω₁)
    | run : ∀ σ Γ e τ φ ω,
      -- ⦰ ⊢ᵣ e : <τ> ! ω
      -- ————————————————————
      -- Γ ⊢ run e : τ⇊ ! ω⇊
      typing_reification σ Γ e (.rep τ) φ ω →
      closed e →
      typing σ Γ 𝟙 (.run e) (escape_ty τ) ⊥ (escape_meffects ω)
    | unit : ∀ σ Γ 𝕊,
      typing σ Γ 𝕊 .unit .unit ⊥ ∅
    | lift_unit : ∀ σ Γ e φ ω,
      typing σ Γ 𝟙 e .unit φ ω →
      typing σ Γ 𝟙 (.lift e) (.fragment .unit) ⊤ ω
    | loc : ∀ σ Γ l,
      l < σ.length →
      typing σ Γ 𝟙 (.loc l) (.ref .nat) ⊥ ∅
    | alloc₁ : ∀ σ Γ 𝕊 e φ ω,
      typing σ Γ 𝕊 e .nat φ ω →
      typing σ Γ 𝕊 (.alloc₁ e) (.ref .nat) φ (ω ∪ { .init 𝕊 })
    | alloc₂ : ∀ σ Γ e φ ω,
      typing σ Γ 𝟙 e (.fragment .nat) φ ω →
      typing σ Γ 𝟙 (.alloc₂ e) (.fragment (.ref .nat)) ⊤ (ω ∪ { .init 𝟚 })
    | load₁ : ∀ σ Γ 𝕊 e φ ω,
      typing σ Γ 𝕊 e (.ref .nat) φ ω →
      typing σ Γ 𝕊 (.load₁ e) .nat φ (ω ∪ { .read 𝕊 })
    | load₂ : ∀ σ Γ e φ ω,
      typing σ Γ 𝟙 e (.fragment (.ref .nat)) φ ω →
      typing σ Γ 𝟙 (.load₂ e) (.fragment .nat) ⊤ (ω ∪ { .read 𝟚 })
    | store₁ : ∀ σ Γ 𝕊 l r φ₀ φ₁ ω₀ ω₁,
      typing σ Γ 𝕊 l (.ref .nat) φ₀ ω₀ →
      typing σ Γ 𝕊 r .nat φ₁ ω₁ →
      typing σ Γ 𝕊 (.store₁ l r) .unit (φ₀ ∪ φ₁) (ω₀ ∪ ω₁ ∪ { .write 𝕊 })
    | store₂ : ∀ σ Γ l r φ₀ φ₁ ω₀ ω₁,
      typing σ Γ 𝟙 l (.fragment (.ref .nat)) φ₀ ω₀ →
      typing σ Γ 𝟙 r (.fragment .nat) φ₁ ω₁ →
      typing σ Γ 𝟙 (.store₂ l r) (.fragment .unit) ⊤ (ω₀ ∪ ω₁ ∪ { .write 𝟚 })

  inductive typing_reification : Store → TEnv → Expr → Ty → REffects → MEffects → Prop
    | pure : ∀ σ Γ e τ ω, typing σ Γ 𝟙 e τ ⊥ ω → typing_reification σ Γ e τ ⊥ ω
    | reify : ∀ σ Γ e τ φ ω, typing σ Γ 𝟙 e (.fragment τ) φ ω → typing_reification σ Γ e (.rep τ) φ ω
end

lemma typing.regular : ∀ σ Γ 𝕊 e τ φ ω, typing σ Γ 𝕊 e τ φ ω → lc e :=
  by
  intros σ Γ 𝕊 e τ φ ω Hτ
  apply
    @typing.rec σ
      (fun Γ 𝕊 e τ φ ω (H : typing σ Γ 𝕊 e τ φ ω) => lc e)
      (fun Γ e τ φ ω (H : typing_reification σ Γ e τ φ ω) => lc e)
  <;> try simp
  <;> intros
  case lam IH =>
    rw [← lc.under_opening]; apply IH
  case lam𝕔 IH =>
    rw [← lc.under_opening]; apply IH
  case app₁ IHf IHarg => simp [IHf, IHarg]
  case app₂ IHf IHarg => simp [IHf, IHarg]
  case lets IHb IHe =>
    constructor; apply IHb
    rw [← lc.under_opening]; apply IHe
  case lets𝕔 IHb IHe =>
    constructor; apply IHb
    rw [← lc.under_opening]; apply IHe
  case store₁ IHl IHr => simp [IHl, IHr]
  case store₂ IHl IHr => simp [IHl, IHr]
  apply Hτ

lemma typing_reification.regular : ∀ σ Γ e τ φ ω, typing_reification σ Γ e τ φ ω → lc e :=
  by
  intros σ Γ e τ φ ω Hτ
  cases Hτ <;> (apply typing.regular; assumption)

lemma typing.closed_at_env : ∀ σ Γ 𝕊 e τ φ ω, typing σ Γ 𝕊 e τ φ ω → closed_at e Γ.length :=
  by
  intros σ Γ 𝕊 e τ φ ω Hτ
  apply
    @typing.rec σ
      (fun Γ 𝕊 e τ φ ω (H : typing σ Γ 𝕊 e τ φ ω) => closed_at e Γ.length)
      (fun Γ e τ φ ω (H : typing_reification σ Γ e τ φ ω) => closed_at e Γ.length)
  <;> try simp
  <;> (intros; try assumption)
  case fvar Hbinds _ =>
    simp [getr_exists_iff_index_lt_length]
    constructor; constructor; apply Hbinds
  case app₁ IHf IHarg => simp [IHf, IHarg]
  case app₂ IHf IHarg => simp [IHf, IHarg]
  case code_fragment Hbinds _ =>
    simp [getr_exists_iff_index_lt_length]
    constructor; constructor; apply Hbinds
  case lets Hclosed IHb _ =>
    constructor; apply IHb; apply Hclosed
  case lets𝕔 Hclosed IHb _ =>
    constructor; apply IHb; apply Hclosed
  case store₁ IHl IHr => simp [IHl, IHr]
  case store₂ IHl IHr => simp [IHl, IHr]
  apply Hτ

lemma typing_reification.closed_at_env : ∀ σ Γ e τ φ ω, typing_reification σ Γ e τ φ ω → closed_at e Γ.length :=
  by
  intros σ Γ e τ φ ω Hτ
  cases Hτ <;> (apply typing.closed_at_env; assumption)

lemma typing.wf : ∀ σ Γ 𝕊 e τ φ ω, typing σ Γ 𝕊 e τ φ ω → wf_at e Γ.length :=
  by
  intros σ Γ 𝕊 e τ φ ω Hτ
  constructor
  apply typing.regular; apply Hτ
  apply typing.closed_at_env; apply Hτ

lemma typing_reification.wf : ∀ σ Γ e τ φ ω, typing_reification σ Γ e τ φ ω → wf_at e Γ.length :=
  by
  intros σ Γ e τ φ ω Hτ
  cases Hτ <;> (apply typing.wf; assumption)

lemma typing.dynamic_impl_pure :
  ∀ σ Γ e τ φ ω,
    typing σ Γ 𝟚 e τ φ ω →
    wbt 𝟚 τ ∧
    φ = ⊥ ∧
    stage_meffects 𝟚 ω :=
  by
  generalize HEq𝕊 : 𝟚 = 𝕊
  intros σ Γ e τ φ ω Hτ
  revert HEq𝕊
  apply @typing.rec σ
    (fun Γ 𝕊 e τ φ ω (H : typing σ Γ 𝕊 e τ φ ω) => 𝟚 = 𝕊 → wbt 𝕊 τ ∧ φ = ⊥ ∧ stage_meffects 𝕊 ω)
    (fun Γ e τ φ ω (H : typing_reification σ Γ e τ φ ω) => true)
  <;> intros
  <;> (try assumption)
  <;> (try contradiction)
  case fvar x _ Hbinds Hwbt HEq𝕊 =>
    constructor
    . apply Hwbt
    constructor
    . simp
    . simp
  case lam Hwbt₀ Hclose IH HEq𝕊 =>
    have ⟨Hwbt₁, Hφ₀, Hω₀⟩ := IH HEq𝕊
    rw [← HEq𝕊]
    rw [← HEq𝕊] at Hwbt₀ Hwbt₁ Hω₀
    constructor
    . constructor; apply Hφ₀
      constructor; apply Hω₀
      constructor; apply Hwbt₀; apply Hwbt₁
    constructor
    . simp
    . simp
  case app₁ IHf IHarg HEq𝕊 =>
    have ⟨Hwbt₁, Hφ₁, Hω₁⟩ := IHf HEq𝕊
    have ⟨Hwbt₂, Hφ₂, Hω₂⟩ := IHarg HEq𝕊
    rw [← HEq𝕊]
    rw [← HEq𝕊] at Hwbt₁ Hwbt₂ Hω₁ Hω₂
    constructor
    . apply Hwbt₁.right.right.right
    constructor
    . simp [Hφ₁, Hφ₂, Hwbt₁.left]
    . apply stage_meffects.union
      apply stage_meffects.union
      apply Hwbt₁.right.left; apply Hω₁; apply Hω₂
  case lit HEq𝕊 => simp [← HEq𝕊]
  case lets Hwbt Hclose IHb IHe HEq𝕊 =>
    have ⟨Hwbt₀, Hφ₀, Hω₀⟩ := IHb HEq𝕊
    have ⟨Hwbt₁, Hφ₁, Hω₁⟩ := IHe HEq𝕊
    constructor
    . apply Hwbt₁
    constructor
    . simp [Hφ₀, Hφ₁]
    . apply stage_meffects.union
      apply Hω₀; apply Hω₁
  case unit HEq𝕊 => simp [← HEq𝕊]
  case load₁ IH HEq𝕊 =>
    have ⟨Hwbt, Hφ, Hω⟩ := IH HEq𝕊
    rw [← HEq𝕊]
    rw [← HEq𝕊] at Hω
    constructor
    . simp
    constructor
    . simp [Hφ]
    . apply stage_meffects.union
      apply Hω; simp
  case alloc₁ IH HEq𝕊 =>
    have ⟨Hwbt, Hφ, Hω⟩ := IH HEq𝕊
    rw [← HEq𝕊]
    rw [← HEq𝕊] at Hω
    constructor
    . simp
    constructor
    . simp [Hφ]
    . apply stage_meffects.union
      apply Hω; simp
  case store₁ IHl IHr HEq𝕊 =>
    have ⟨Hwbt₀, Hφ₀, Hω₀⟩ := IHl HEq𝕊
    have ⟨Hwbt₁, Hφ₁, Hω₁⟩ := IHr HEq𝕊
    rw [← HEq𝕊]
    rw [← HEq𝕊] at Hω₀ Hω₁
    constructor
    . simp
    constructor
    . simp [Hφ₀, Hφ₁]
    . apply stage_meffects.union
      apply stage_meffects.union
      apply Hω₀; apply Hω₁; simp
  case pure => simp
  case reify => simp

lemma typing_reification_code :
  ∀ σ Γ e τ φ ω,
    typing_reification σ Γ (.code e) (.rep τ) φ ω →
    typing σ Γ 𝟚 e τ ⊥ ω :=
  by
  intros σ Γ e τ φ ω Hτ
  cases Hτ
  case pure Hτ =>
    cases Hτ
    case code_rep Hτ => apply Hτ
  case reify Hτ =>
    cases Hτ
    case code_fragment Hwbt Hbinds =>
      apply typing.fvar; apply Hbinds; apply Hwbt
