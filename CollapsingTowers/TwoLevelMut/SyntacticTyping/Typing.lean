import CollapsingTowers.TwoLevelMut.Syntax.Defs
import CollapsingTowers.TwoLevelMut.SyntacticTyping.Env
import CollapsingTowers.TwoLevelMut.OperationalSemantics.Defs

mutual
  inductive typing : HEnv → TEnv → Stage → Expr → Ty → Effect → Prop where
    | fvar : ∀ Ω Γ 𝕊 x τ,
      binds x (τ, 𝕊) Γ →
      wbt 𝕊 τ →
      typing Ω Γ 𝕊 (.fvar x) τ ⊥
    | lam : ∀ Ω Γ 𝕊 e τ𝕒 τ𝕓 φ,
      typing Ω ((τ𝕒, 𝕊) :: Γ) 𝕊 ({0 ↦ Γ.length} e) τ𝕓 φ →
      wbt 𝕊 τ𝕒 →
      closed_at e Γ.length →
      typing Ω Γ 𝕊 (.lam e) (.arrow τ𝕒 τ𝕓 φ) ⊥
    | lift_lam : ∀ Ω Γ e τ𝕒 τ𝕓 φ₀ φ₁,
      typing Ω Γ 𝟙 e (.arrow (.fragment τ𝕒) (.fragment τ𝕓) φ₀) φ₁ →
      typing Ω Γ 𝟙 (.lift e) (.fragment (.arrow τ𝕒 τ𝕓 ⊥)) ⊤
    | app₁ : ∀ Ω Γ 𝕊 f arg τ𝕒 τ𝕓 φ₀ φ₁ φ₂,
      typing Ω Γ 𝕊 f (.arrow τ𝕒 τ𝕓 φ₀) φ₁ →
      typing Ω Γ 𝕊 arg τ𝕒 φ₂ →
      typing Ω Γ 𝕊 (.app₁ f arg) τ𝕓 (φ₀ ∪ φ₁ ∪ φ₂)
    | app₂ : ∀ Ω Γ f arg τ𝕒 τ𝕓 φ₀ φ₁,
      typing Ω Γ 𝟙 f (.fragment (.arrow τ𝕒 τ𝕓 ⊥)) φ₀ →
      typing Ω Γ 𝟙 arg (.fragment τ𝕒) φ₁ →
      typing Ω Γ 𝟙 (.app₂ f arg) (.fragment τ𝕓) ⊤
    | lit : ∀ Ω Γ 𝕊 n,
      typing Ω Γ 𝕊 (.lit n) .nat ⊥
    | lift_lit : ∀ Ω Γ n φ,
      typing Ω Γ 𝟙 n .nat φ →
      typing Ω Γ 𝟙 (.lift n) (.fragment .nat) ⊤
    | code_fragment : ∀ Ω Γ x τ,
      binds x (τ, 𝟚) Γ →
      wbt 𝟚 τ →
      typing Ω Γ 𝟙 (.code (.fvar x)) (.fragment τ) ⊥
    | code_rep : ∀ Ω Γ e τ,
      typing Ω Γ 𝟚 e τ ⊥ →
      typing Ω Γ 𝟙 (.code e) (.rep τ) ⊥
    | reflect : ∀ Ω Γ e τ,
      typing Ω Γ 𝟚 e τ ⊥ →
      typing Ω Γ 𝟙 (.reflect e) (.fragment τ) ⊤
    | lam𝕔 : ∀ Ω Γ e τ𝕒 τ𝕓 φ,
      typing_reification Ω ((τ𝕒, 𝟚) :: Γ) ({0 ↦ Γ.length} e) (.rep τ𝕓) φ →
      wbt 𝟚 τ𝕒 →
      closed_at e Γ.length →
      typing Ω Γ 𝟙 (.lam𝕔 e) (.fragment (.arrow τ𝕒 τ𝕓 ⊥)) ⊤
    | lets : ∀ Ω Γ 𝕊 b e τ𝕒 τ𝕓 φ₀ φ₁,
      typing Ω Γ 𝕊 b τ𝕒 φ₀ →
      typing Ω ((τ𝕒, 𝕊) :: Γ) 𝕊 ({0 ↦ Γ.length} e) τ𝕓 φ₁ →
      wbt 𝕊 τ𝕒 →
      closed_at e Γ.length →
      typing Ω Γ 𝕊 (.lets b e) τ𝕓 (φ₀ ∪ φ₁)
    | lets𝕔 : ∀ Ω Γ b e τ𝕒 τ𝕓 φ,
      typing Ω Γ 𝟚 b τ𝕒 ⊥ →
      typing_reification Ω ((τ𝕒, 𝟚) :: Γ) ({0 ↦ Γ.length} e) (.rep τ𝕓) φ →
      wbt 𝟚 τ𝕒 →
      closed_at e Γ.length →
      typing Ω Γ 𝟙 (.lets𝕔 b e) (.rep τ𝕓) ⊥
    | run : ∀ Ω Γ e τ φ,
      typing_reification Ω Γ e (.rep τ) φ →
      closed e →
      typing Ω Γ 𝟙 (.run e) τ ⊥
    | unit : ∀ Ω Γ 𝕊,
      typing Ω Γ 𝕊 .unit .unit ⊥
    | loc : ∀ Ω Γ l,
      binds l .nat Ω →
      typing Ω Γ 𝟙 (.loc l) (.ref .nat) ⊥
    | load₁ : ∀ Ω Γ 𝕊 e φ,
      typing Ω Γ 𝕊 e (.ref .nat) φ →
      typing Ω Γ 𝕊 (.load₁ e) .nat φ
    | load₂ : ∀ Ω Γ e φ,
      typing Ω Γ 𝟙 e (.fragment (.ref .nat)) φ →
      typing Ω Γ 𝟙 (.load₂ e) (.fragment .nat) ⊤
    | alloc₁ : ∀ Ω Γ 𝕊 e φ,
      typing Ω Γ 𝕊 e .nat φ →
      typing Ω Γ 𝕊 (.alloc₁ e) (.ref .nat) φ
    | alloc₂ : ∀ Ω Γ e φ,
      typing Ω Γ 𝟙 e (.fragment .nat) φ →
      typing Ω Γ 𝟙 (.alloc₂ e) (.fragment (.ref .nat)) ⊤
    | store₁ : ∀ Ω Γ 𝕊 l r φ₀ φ₁,
      typing Ω Γ 𝕊 l (.ref .nat) φ₀ →
      typing Ω Γ 𝕊 r .nat φ₁ →
      typing Ω Γ 𝕊 (.store₁ l r) .unit (φ₀ ∪ φ₁)
    | store₂ : ∀ Ω Γ l r φ₀ φ₁,
      typing Ω Γ 𝟙 l (.fragment (.ref .nat)) φ₀ →
      typing Ω Γ 𝟙 r (.fragment .nat) φ₁ →
      typing Ω Γ 𝟙 (.store₂ l r) (.fragment .unit) ⊤

  inductive typing_reification : HEnv → TEnv → Expr → Ty → Effect → Prop
    | pure : ∀ Ω Γ e τ, typing Ω Γ 𝟙 e τ ⊥ → typing_reification Ω Γ e τ ⊥
    | reify : ∀ Ω Γ e τ φ, typing Ω Γ 𝟙 e (.fragment τ) φ → typing_reification Ω Γ e (.rep τ) φ
end

lemma typing.regular : ∀ Ω Γ 𝕊 e τ φ, typing Ω Γ 𝕊 e τ φ → lc e :=
  by
  intros Ω Γ 𝕊 e τ φ Hτ
  apply
    @typing.rec Ω
      (fun Γ 𝕊 e τ φ (H : typing Ω Γ 𝕊 e τ φ) => lc e)
      (fun Γ e τ φ (H : typing_reification Ω Γ e τ φ) => lc e)
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

lemma typing_reification.regular : ∀ Ω Γ e τ φ, typing_reification Ω Γ e τ φ → lc e :=
  by
  intros Ω Γ e τ φ Hτ
  cases Hτ <;> (apply typing.regular; assumption)

lemma typing.closed_at_env : ∀ Ω Γ 𝕊 e τ φ, typing Ω Γ 𝕊 e τ φ → closed_at e Γ.length :=
  by
  intros Ω Γ 𝕊 e τ φ Hτ
  apply
    @typing.rec Ω
      (fun Γ 𝕊 e τ φ (H : typing Ω Γ 𝕊 e τ φ) => closed_at e Γ.length)
      (fun Γ e τ φ (H : typing_reification Ω Γ e τ φ) => closed_at e Γ.length)
  <;> try simp
  <;> (intros; try assumption)
  case fvar HBinds _ =>
    simp [getr_exists_iff_index_lt_length]
    constructor; constructor; apply HBinds
  case app₁ IHf IHarg => simp [IHf, IHarg]
  case app₂ IHf IHarg => simp [IHf, IHarg]
  case code_fragment HBinds _ =>
    simp [getr_exists_iff_index_lt_length]
    constructor; constructor; apply HBinds
  case lets Hclosed IHb _ =>
    constructor; apply IHb; apply Hclosed
  case lets𝕔 Hclosed IHb _ =>
    constructor; apply IHb; apply Hclosed
  case store₁ IHl IHr => simp [IHl, IHr]
  case store₂ IHl IHr => simp [IHl, IHr]
  apply Hτ

lemma typing_reification.closed_at_env : ∀ Ω Γ e τ φ, typing_reification Ω Γ e τ φ → closed_at e Γ.length :=
  by
  intros Ω Γ e τ φ Hτ
  cases Hτ <;> (apply typing.closed_at_env; assumption)

lemma typing.wf : ∀ Ω Γ 𝕊 e τ φ, typing Ω Γ 𝕊 e τ φ → wf_at e Γ.length :=
  by
  intros Ω Γ 𝕊 e τ φ Hτ
  constructor
  apply typing.regular; apply Hτ
  apply typing.closed_at_env; apply Hτ

lemma typing_reification.wf : ∀ Ω Γ e τ φ, typing_reification Ω Γ e τ φ → wf_at e Γ.length :=
  by
  intros Ω Γ e τ φ Hτ
  cases Hτ <;> (apply typing.wf; assumption)

lemma typing.dynamic_impl_pure : ∀ Ω Γ e τ φ, typing Ω Γ 𝟚 e τ φ → wbt 𝟚 τ ∧ φ = ⊥ :=
  by
  generalize HEq𝕊 : 𝟚 = 𝕊
  intros Ω Γ e τ φ Hτ
  revert HEq𝕊
  apply @typing.rec Ω
    (fun Γ 𝕊 e τ φ (H : typing Ω Γ 𝕊 e τ φ) => 𝟚 = 𝕊 → wbt 𝕊 τ ∧ φ = ⊥)
    (fun Γ e τ φ (H : typing_reification Ω Γ e τ φ) => true)
  <;> intros
  <;> (try assumption)
  <;> (try contradiction)
  case fvar x _ HBinds Hwbt HEq𝕊 =>
    constructor; apply Hwbt; rfl
  case lam Hwbt₀ Hclose IH HEq𝕊 =>
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
  case lets Hwbt Hclose IHb IHe HEq𝕊 =>
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

lemma typing.dynamic_impl_grounded : ∀ Ω Γ e τ φ, typing Ω Γ 𝟚 e τ φ → grounded e :=
  by
  generalize HEq𝕊 : 𝟚 = 𝕊
  intros Ω Γ e τ φ Hτ
  revert HEq𝕊
  apply @typing.rec Ω
    (fun Γ 𝕊 e τ φ (H : typing Ω Γ 𝕊 e τ φ) => 𝟚 = 𝕊 → grounded e)
    (fun Γ e τ φ (H : typing_reification Ω Γ e τ φ) => true)
  <;> intros
  <;> (try assumption)
  <;> (try contradiction)
  <;> simp
  case lam IH HEq𝕊 =>
    rw [grounded.under_opening]; apply IH; apply HEq𝕊
  case app₁ IH₀ IH₁ HEq𝕊 =>
    constructor
    apply IH₀; apply HEq𝕊
    apply IH₁; apply HEq𝕊
  case lets IH₀ IH₁ HEq𝕊 =>
    constructor
    apply IH₀; apply HEq𝕊
    rw [grounded.under_opening]; apply IH₁; apply HEq𝕊
  case load₁ IH HEq𝕊 =>
    apply IH; apply HEq𝕊
  case alloc₁ IH HEq𝕊 =>
    apply IH; apply HEq𝕊
  case store₁ IH₀ IH₁ HEq𝕊 =>
    constructor
    apply IH₀; apply HEq𝕊
    apply IH₁; apply HEq𝕊

lemma typing.dynamic_impl_loc_free : ∀ Ω Γ e τ φ, typing Ω Γ 𝟚 e τ φ → typing ⦰ᴴ Γ 𝟚 e τ φ :=
  by
  generalize HEq𝕊 : 𝟚 = 𝕊
  intros Ω Γ e τ φ Hτ
  revert HEq𝕊
  apply @typing.rec Ω
    (fun Γ 𝕊 e τ φ (H : typing Ω Γ 𝕊 e τ φ) => 𝟚 = 𝕊 → typing ⦰ᴴ Γ 𝕊 e τ φ)
    (fun Γ e τ φ (H : typing_reification Ω Γ e τ φ) => true)
  <;> intros
  <;> (try contradiction)
  case fvar HBinds Hwbt HEq𝕊 =>
    apply typing.fvar
    apply HBinds; apply Hwbt
  case lam Hwbt Hclosed IH HEq𝕊 =>
    apply typing.lam
    . apply IH; apply HEq𝕊
    . apply Hwbt
    . apply Hclosed
  case app₁ IH₀ IH₁ HEq𝕊 =>
    apply typing.app₁
    . apply IH₀; apply HEq𝕊
    . apply IH₁; apply HEq𝕊
  case lit => apply typing.lit
  case lets Hwbt Hclosed IH₀ IH₁ HEq𝕊 =>
    apply typing.lets
    . apply IH₀; apply HEq𝕊
    . apply IH₁; apply HEq𝕊
    . apply Hwbt
    . apply Hclosed
  case unit => apply typing.unit
  case load₁ IH HEq𝕊 =>
    apply typing.load₁
    apply IH; apply HEq𝕊
  case alloc₁ IH HEq𝕊 =>
    apply typing.alloc₁
    apply IH; apply HEq𝕊
  case store₁ IH₀ IH₁ HEq𝕊 =>
    apply typing.store₁
    . apply IH₀; apply HEq𝕊
    . apply IH₁; apply HEq𝕊
  case pure => rfl
  case reify => rfl
  apply Hτ

lemma typing_reification_code :
  ∀ Ω Γ e τ φ,
    typing_reification Ω Γ (.code e) (.rep τ) φ →
    typing Ω Γ 𝟚 e τ ⊥ :=
  by
  intros Ω Γ e τ φ Hτ
  cases Hτ
  case pure Hτ =>
    cases Hτ
    case code_rep Hτ => apply Hτ
  case reify Hτ =>
    cases Hτ
    case code_fragment Hwbt HBinds =>
      apply typing.fvar; apply HBinds; apply Hwbt
