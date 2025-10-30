import CollapsingTowers.TwoLevelMut.Syntax.Defs
import CollapsingTowers.TwoLevelMut.SyntacticTyping.Env
import CollapsingTowers.TwoLevelMut.OperationalSemantics.Defs

mutual
  inductive typing : TEnv → Stage → Expr → Ty → Effect → Bool → Prop where
    | fvar : ∀ Γ 𝕊 x τ,
      binds x (τ, 𝕊) Γ →
      wbt 𝕊 τ →
      typing Γ 𝕊 (.fvar x) τ ⊥ ⊥
    | lam : ∀ Γ 𝕊 e τ𝕒 τ𝕓 φ ω,
      typing ((τ𝕒, 𝕊) :: Γ) 𝕊 ({0 ↦ Γ.length} e) τ𝕓 φ ω →
      wbt 𝕊 τ𝕒 →
      closed_at e Γ.length →
      typing Γ 𝕊 (.lam e) (.arrow τ𝕒 τ𝕓 φ) ⊥ ω
    | lift_lam : ∀ Γ e τ𝕒 τ𝕓 φ₀ φ₁ ω,
      typing Γ 𝟙 e (.arrow (.fragment τ𝕒) (.fragment τ𝕓) φ₀) φ₁ ω →
      typing Γ 𝟙 (.lift e) (.fragment (.arrow τ𝕒 τ𝕓 ⊥)) ⊤ ω
    | app₁ : ∀ Γ 𝕊 f arg τ𝕒 τ𝕓 φ₀ φ₁ φ₂ ω₁ ω₂,
      typing Γ 𝕊 f (.arrow τ𝕒 τ𝕓 φ₀) φ₁ ω₁ →
      typing Γ 𝕊 arg τ𝕒 φ₂ ω₂ →
      typing Γ 𝕊 (.app₁ f arg) τ𝕓 (φ₀ ∪ φ₁ ∪ φ₂) (ω₁ ∨ ω₂)
    | app₂ : ∀ Γ f arg τ𝕒 τ𝕓 φ₁ φ₂ ω₁ ω₂,
      typing Γ 𝟙 f (.fragment (.arrow τ𝕒 τ𝕓 ⊥)) φ₁ ω₁ →
      typing Γ 𝟙 arg (.fragment τ𝕒) φ₂ ω₂ →
      typing Γ 𝟙 (.app₂ f arg) (.fragment τ𝕓) ⊤ (ω₁ ∨ ω₂)
    | lit : ∀ Γ 𝕊 n,
      typing Γ 𝕊 (.lit n) .nat ⊥ ⊥
    | lift_lit : ∀ Γ n φ ω,
      typing Γ 𝟙 n .nat φ ω →
      typing Γ 𝟙 (.lift n) (.fragment .nat) ⊤ ω
    | code_fragment : ∀ Γ x τ,
      binds x (τ, 𝟚) Γ →
      wbt 𝟚 τ →
      typing Γ 𝟙 (.code (.fvar x)) (.fragment τ) ⊥ ⊥
    | code_rep : ∀ Γ e τ ω,
      typing Γ 𝟚 e τ ⊥ ω →
      typing Γ 𝟙 (.code e) (.rep τ) ⊥ ω
    | reflect : ∀ Γ e τ ω,
      typing Γ 𝟚 e τ ⊥ ω →
      typing Γ 𝟙 (.reflect e) (.fragment τ) ⊤ ω
    | lam𝕔 : ∀ Γ e τ𝕒 τ𝕓 φ ω,
      typing_reification ((τ𝕒, 𝟚) :: Γ) ({0 ↦ Γ.length} e) (.rep τ𝕓) φ ω →
      wbt 𝟚 τ𝕒 →
      closed_at e Γ.length →
      typing Γ 𝟙 (.lam𝕔 e) (.fragment (.arrow τ𝕒 τ𝕓 ⊥)) ⊤ ω
    | lets : ∀ Γ 𝕊 b e τ𝕒 τ𝕓 φ₀ φ₁ ω₀ ω₁,
      typing Γ 𝕊 b τ𝕒 φ₀ ω₀ →
      typing ((τ𝕒, 𝕊) :: Γ) 𝕊 ({0 ↦ Γ.length} e) τ𝕓 φ₁ ω₁ →
      wbt 𝕊 τ𝕒 →
      closed_at e Γ.length →
      typing Γ 𝕊 (.lets b e) τ𝕓 (φ₀ ∪ φ₁) (ω₀ ∨ ω₁)
    | lets𝕔 : ∀ Γ b e τ𝕒 τ𝕓 φ₁ ω₀ ω₁,
      typing Γ 𝟚 b τ𝕒 ⊥ ω₀ →
      typing_reification ((τ𝕒, 𝟚) :: Γ) ({0 ↦ Γ.length} e) (.rep τ𝕓) φ₁ ω₁ →
      wbt 𝟚 τ𝕒 →
      closed_at e Γ.length →
      typing Γ 𝟙 (.lets𝕔 b e) (.rep τ𝕓) ⊥ (ω₀ ∨ ω₁)
    | run : ∀ Γ e τ φ,
      typing_reification Γ e (.rep τ) φ ⊥ →
      closed e →
      typing Γ 𝟙 (.run e) τ ⊥ ⊥
    | unit : ∀ Γ 𝕊,
      typing Γ 𝕊 .unit .unit ⊥ ⊥
    | lift_unit : ∀ Γ e φ ω,
      typing Γ 𝟙 e .unit φ ω →
      typing Γ 𝟙 (.lift e) (.fragment .unit) ⊤ ω
    | alloc₁ : ∀ Γ e φ ω,
      typing Γ 𝟚 e .nat φ ω →
      typing Γ 𝟚 (.alloc₁ e) (.ref .nat) φ ⊤
    | alloc₂ : ∀ Γ e φ ω,
      typing Γ 𝟙 e (.fragment .nat) φ ω →
      typing Γ 𝟙 (.alloc₂ e) (.fragment (.ref .nat)) ⊤ ⊤
    | load₁ : ∀ Γ e φ ω,
      typing Γ 𝟚 e (.ref .nat) φ ω →
      typing Γ 𝟚 (.load₁ e) .nat φ ⊤
    | load₂ : ∀ Γ e φ ω,
      typing Γ 𝟙 e (.fragment (.ref .nat)) φ ω →
      typing Γ 𝟙 (.load₂ e) (.fragment .nat) ⊤ ⊤
    | store₁ : ∀ Γ l r φ₀ φ₁ ω₀ ω₁,
      typing Γ 𝟚 l (.ref .nat) φ₀ ω₀ →
      typing Γ 𝟚 r .nat φ₁ ω₁ →
      typing Γ 𝟚 (.store₁ l r) .unit (φ₀ ∪ φ₁) ⊤
    | store₂ : ∀ Γ l r φ₀ φ₁ ω₀ ω₁,
      typing Γ 𝟙 l (.fragment (.ref .nat)) φ₀ ω₀ →
      typing Γ 𝟙 r (.fragment .nat) φ₁ ω₁ →
      typing Γ 𝟙 (.store₂ l r) (.fragment .unit) ⊤ ⊤

  inductive typing_reification : TEnv → Expr → Ty → Effect → Bool → Prop
    | pure : ∀ Γ e τ ω, typing Γ 𝟙 e τ ⊥ ω → typing_reification Γ e τ ⊥ ω
    | reify : ∀ Γ e τ φ ω, typing Γ 𝟙 e (.fragment τ) φ ω → typing_reification Γ e (.rep τ) φ ω
end

lemma typing.regular : ∀ Γ 𝕊 e τ φ ω, typing Γ 𝕊 e τ φ ω → lc e :=
  by
  intros Γ 𝕊 e τ φ ω Hτ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ φ ω (H : typing Γ 𝕊 e τ φ ω) => lc e)
      (fun Γ e τ φ ω (H : typing_reification Γ e τ φ ω) => lc e)
  <;> try simp [-Bool.forall_bool]
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

lemma typing_reification.regular : ∀ Γ e τ φ ω, typing_reification Γ e τ φ ω → lc e :=
  by
  intros Γ e τ φ ω Hτ
  cases Hτ <;> (apply typing.regular; assumption)

lemma typing.closed_at_env : ∀ Γ 𝕊 e τ φ ω, typing Γ 𝕊 e τ φ ω → closed_at e Γ.length :=
  by
  intros Γ 𝕊 e τ φ ω Hτ
  apply
    @typing.rec
      (fun Γ 𝕊 e τ φ ω (H : typing Γ 𝕊 e τ φ ω) => closed_at e Γ.length)
      (fun Γ e τ φ ω (H : typing_reification Γ e τ φ ω) => closed_at e Γ.length)
  <;> try simp [-Bool.forall_bool]
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

lemma typing_reification.closed_at_env : ∀ Γ e τ φ ω, typing_reification Γ e τ φ ω → closed_at e Γ.length :=
  by
  intros Γ e τ φ ω Hτ
  cases Hτ <;> (apply typing.closed_at_env; assumption)

lemma typing.wf : ∀ Γ 𝕊 e τ φ ω, typing Γ 𝕊 e τ φ ω → wf_at e Γ.length :=
  by
  intros Γ 𝕊 e τ φ ω Hτ
  constructor
  apply typing.regular; apply Hτ
  apply typing.closed_at_env; apply Hτ

lemma typing_reification.wf : ∀ Γ e τ φ ω, typing_reification Γ e τ φ ω → wf_at e Γ.length :=
  by
  intros Γ e τ φ ω Hτ
  cases Hτ <;> (apply typing.wf; assumption)

lemma typing.dynamic_impl_pure : ∀ Γ e τ φ ω, typing Γ 𝟚 e τ φ ω → wbt 𝟚 τ ∧ φ = ⊥ :=
  by
  generalize HEq𝕊 : 𝟚 = 𝕊
  intros Γ e τ φ ω Hτ
  revert HEq𝕊
  apply @typing.rec
    (fun Γ 𝕊 e τ φ ω (H : typing Γ 𝕊 e τ φ ω) => 𝟚 = 𝕊 → wbt 𝕊 τ ∧ φ = ⊥)
    (fun Γ e τ φ ω (H : typing_reification Γ e τ φ ω) => true)
  <;> intros
  <;> (try assumption)
  <;> (try contradiction)
  case fvar Hwbt HEq𝕊 =>
    constructor; apply Hwbt; rfl
  case lam Hwbt₀ _ IH HEq𝕊 =>
    have ⟨Hwbt₁, Hφ₀⟩ := IH HEq𝕊
    rw [← HEq𝕊]
    rw [← HEq𝕊] at Hwbt₀ Hwbt₁
    constructor
    . constructor
      apply Hφ₀; constructor
      apply Hwbt₀; apply Hwbt₁
    . rfl
  case app₁ IHf IHarg HEq𝕊 =>
    have ⟨Hwbt₁, Hφ₁⟩ := IHf HEq𝕊
    have ⟨Hwbt₂, Hφ₂⟩ := IHarg HEq𝕊
    rw [← HEq𝕊]
    rw [← HEq𝕊] at Hwbt₁ Hwbt₂
    constructor
    . apply Hwbt₁.right.right
    . simp [Hφ₁, Hφ₂, Hwbt₁.left]
  case lit HEq𝕊 =>
    rw [← HEq𝕊]
    constructor
    . simp
    . rfl
  case lets IHb IHe HEq𝕊 =>
    have ⟨Hwbt₀, Hφ₀⟩ := IHb HEq𝕊
    have ⟨Hwbt₁, Hφ₁⟩ := IHe HEq𝕊
    constructor
    . apply Hwbt₁
    . simp [Hφ₀, Hφ₁]
  case unit HEq𝕊 =>
    rw [← HEq𝕊]
    constructor
    . simp
    . rfl
  case load₁ IH HEq𝕊 =>
    have ⟨Hwbt, Hφ⟩ := IH HEq𝕊
    rw [← HEq𝕊]
    constructor
    . simp
    . simp [Hφ]
  case alloc₁ IH HEq𝕊 =>
    have ⟨Hwbt, Hφ⟩ := IH HEq𝕊
    rw [← HEq𝕊]
    constructor
    . simp
    . simp [Hφ]
  case store₁ IHl IHr HEq𝕊 =>
    have ⟨Hwbt₀, Hφ₀⟩ := IHl HEq𝕊
    have ⟨Hwbt₁, Hφ₁⟩ := IHr HEq𝕊
    rw [← HEq𝕊]
    constructor
    . simp
    . simp [Hφ₀, Hφ₁]
  case pure => simp
  case reify => simp

lemma typing_reification_code :
  ∀ Γ e τ φ ω,
    typing_reification Γ (.code e) (.rep τ) φ ω →
    typing Γ 𝟚 e τ ⊥ ω :=
  by
  intros Γ e τ φ ω Hτ
  cases Hτ
  case pure Hτ =>
    cases Hτ
    case code_rep Hτ => apply Hτ
  case reify Hτ =>
    cases Hτ
    case code_fragment Hwbt Hbinds =>
      apply typing.fvar; apply Hbinds; apply Hwbt
