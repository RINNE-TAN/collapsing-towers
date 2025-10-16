import CollapsingTowers.TwoLevelMut.Syntax.Defs
import CollapsingTowers.TwoLevelMut.SyntacticTyping.Env
import CollapsingTowers.TwoLevelMut.OperationalSemantics.Defs
mutual
  inductive typing : Store → TEnv → Stage → Expr → Ty → Effects → Prop where
    | fvar : ∀ σ Γ 𝕊 x τ,
      binds x (τ, 𝕊) Γ →
      wbt 𝕊 τ →
      typing σ Γ 𝕊 (.fvar x) τ ⊥
    | lam : ∀ σ Γ 𝕊 e τ𝕒 τ𝕓 φ,
      typing σ ((τ𝕒, 𝕊) :: Γ) 𝕊 ({0 ↦ Γ.length} e) τ𝕓 φ →
      wbt 𝕊 τ𝕒 →
      closed_at e Γ.length →
      typing σ Γ 𝕊 (.lam e) (.arrow τ𝕒 τ𝕓 φ) ⊥
    | lift_lam : ∀ σ Γ e τ𝕒 τ𝕓 φ₀ φ₁,
      typing σ Γ 𝟙 e (.arrow (.fragment τ𝕒) (.fragment τ𝕓) φ₀) φ₁ →
      wbt_effects 𝟚 (φ₀ \ { .reify }) →
      typing σ Γ 𝟙 (.lift e) (.fragment (.arrow τ𝕒 τ𝕓 (φ₀ \ { .reify }))) (φ₁ ∪ { .reify })
    | app₁ : ∀ σ Γ 𝕊 f arg τ𝕒 τ𝕓 φ₀ φ₁ φ₂,
      typing σ Γ 𝕊 f (.arrow τ𝕒 τ𝕓 φ₀) φ₁ →
      typing σ Γ 𝕊 arg τ𝕒 φ₂ →
      typing σ Γ 𝕊 (.app₁ f arg) τ𝕓 (φ₀ ∪ φ₁ ∪ φ₂)
    | app₂ : ∀ σ Γ f arg τ𝕒 τ𝕓 φ₀ φ₁ φ₂,
      typing σ Γ 𝟙 f (.fragment (.arrow τ𝕒 τ𝕓 φ₀)) φ₁ →
      typing σ Γ 𝟙 arg (.fragment τ𝕒) φ₂ →
      typing σ Γ 𝟙 (.app₂ f arg) (.fragment τ𝕓) (φ₀ ∪ φ₁ ∪ φ₂ ∪ { .reify })
    | lit : ∀ σ Γ 𝕊 n,
      typing σ Γ 𝕊 (.lit n) .nat ⊥
    | lift_lit : ∀ σ Γ n φ,
      typing σ Γ 𝟙 n .nat φ →
      typing σ Γ 𝟙 (.lift n) (.fragment .nat) (φ ∪ { .reify })
    | code_fragment : ∀ σ Γ x τ,
      binds x (τ, 𝟚) Γ →
      wbt 𝟚 τ →
      typing σ Γ 𝟙 (.code (.fvar x)) (.fragment τ) ⊥
    | code_rep : ∀ σ Γ e τ φ,
      typing σ Γ 𝟚 e τ φ →
      typing σ Γ 𝟙 (.code e) (.rep τ) φ
    | reflect : ∀ σ Γ e τ φ,
      typing σ Γ 𝟚 e τ φ →
      typing σ Γ 𝟙 (.reflect e) (.fragment τ) (φ ∪ { .reify })
    | lam𝕔 : ∀ σ Γ e τ𝕒 τ𝕓 φ,
      typing_reification σ ((τ𝕒, 𝟚) :: Γ) ({0 ↦ Γ.length} e) (.rep τ𝕓) φ →
      wbt 𝟚 τ𝕒 →
      closed_at e Γ.length →
      wbt_effects 𝟚 (φ \ { .reify }) →
      typing σ Γ 𝟙 (.lam𝕔 e) (.fragment (.arrow τ𝕒 τ𝕓 (φ \ { .reify }))) { .reify }
    | lets : ∀ σ Γ 𝕊 b e τ𝕒 τ𝕓 φ₀ φ₁,
      typing σ Γ 𝕊 b τ𝕒 φ₀ →
      typing σ ((τ𝕒, 𝕊) :: Γ) 𝕊 ({0 ↦ Γ.length} e) τ𝕓 φ₁ →
      wbt 𝕊 τ𝕒 →
      closed_at e Γ.length →
      typing σ Γ 𝕊 (.lets b e) τ𝕓 (φ₀ ∪ φ₁)
    | lets𝕔 : ∀ σ Γ b e τ𝕒 τ𝕓 φ,
      typing σ Γ 𝟚 b τ𝕒 ⊥ →
      typing_reification σ ((τ𝕒, 𝟚) :: Γ) ({0 ↦ Γ.length} e) (.rep τ𝕓) φ →
      wbt 𝟚 τ𝕒 →
      closed_at e Γ.length →
      typing σ Γ 𝟙 (.lets𝕔 b e) (.rep τ𝕓) (φ \ { .reify })
    | run : ∀ σ Γ e τ φ,
      typing_reification σ Γ e (.rep τ) φ →
      closed e →
      typing σ Γ 𝟙 (.run e) τ (escape_effects φ \ { .reify })
    | unit : ∀ σ Γ 𝕊,
      typing σ Γ 𝕊 .unit .unit ⊥
    | lift_unit : ∀ σ Γ e φ,
      typing σ Γ 𝟙 e .unit φ →
      typing σ Γ 𝟙 (.lift e) (.fragment .unit) (φ ∪ { .reify })
    | loc : ∀ σ Γ l,
      l < σ.length →
      typing σ Γ 𝟙 (.loc l) (.ref .nat) ⊥
    | alloc₁ : ∀ σ Γ 𝕊 e φ,
      typing σ Γ 𝕊 e .nat φ →
      typing σ Γ 𝕊 (.alloc₁ e) (.ref .nat) (φ ∪ { .mutate 𝕊 })
    | alloc₂ : ∀ σ Γ e φ,
      typing σ Γ 𝟙 e (.fragment .nat) φ →
      typing σ Γ 𝟙 (.alloc₂ e) (.fragment (.ref .nat)) (φ ∪ { .mutate 𝟚 } ∪ { .reify })
    | load₁ : ∀ σ Γ 𝕊 e φ,
      typing σ Γ 𝕊 e (.ref .nat) φ →
      typing σ Γ 𝕊 (.load₁ e) .nat (φ ∪ { .mutate 𝕊 })
    | load₂ : ∀ σ Γ e φ,
      typing σ Γ 𝟙 e (.fragment (.ref .nat)) φ →
      typing σ Γ 𝟙 (.load₂ e) (.fragment .nat) (φ ∪ { .mutate 𝟚 } ∪ { .reify })
    | store₁ : ∀ σ Γ 𝕊 l r φ₀ φ₁,
      typing σ Γ 𝕊 l (.ref .nat) φ₀ →
      typing σ Γ 𝕊 r .nat φ₁ →
      typing σ Γ 𝕊 (.store₁ l r) .unit (φ₀ ∪ φ₁ ∪ { .mutate 𝕊 })
    | store₂ : ∀ σ Γ l r φ₀ φ₁,
      typing σ Γ 𝟙 l (.fragment (.ref .nat)) φ₀ →
      typing σ Γ 𝟙 r (.fragment .nat) φ₁ →
      typing σ Γ 𝟙 (.store₂ l r) (.fragment .unit) (φ₀ ∪ φ₁ ∪ { .mutate 𝟚 } ∪ { .reify })

  inductive typing_reification : Store → TEnv → Expr → Ty → Effects → Prop
    | pure : ∀ σ Γ e τ φ,
      .reify ∉ φ →
      typing σ Γ 𝟙 e τ φ →
      typing_reification σ Γ e τ φ
    | reify : ∀ σ Γ e τ φ,
      typing σ Γ 𝟙 e (.fragment τ) φ →
      typing_reification σ Γ e (.rep τ) φ
end

lemma typing.regular : ∀ σ Γ 𝕊 e τ φ, typing σ Γ 𝕊 e τ φ → lc e :=
  by
  intros σ Γ 𝕊 e τ φ Hτ
  apply
    @typing.rec σ
      (fun Γ 𝕊 e τ φ (H : typing σ Γ 𝕊 e τ φ) => lc e)
      (fun Γ e τ φ (H : typing_reification σ Γ e τ φ) => lc e)
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

lemma typing_reification.regular : ∀ σ Γ e τ φ, typing_reification σ Γ e τ φ → lc e :=
  by
  intros σ Γ e τ φ Hτ
  cases Hτ <;> (apply typing.regular; assumption)

lemma typing.closed_at_env : ∀ σ Γ 𝕊 e τ φ, typing σ Γ 𝕊 e τ φ → closed_at e Γ.length :=
  by
  intros σ Γ 𝕊 e τ φ Hτ
  apply
    @typing.rec σ
      (fun Γ 𝕊 e τ φ (H : typing σ Γ 𝕊 e τ φ) => closed_at e Γ.length)
      (fun Γ e τ φ (H : typing_reification σ Γ e τ φ) => closed_at e Γ.length)
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

lemma typing_reification.closed_at_env : ∀ σ Γ e τ φ, typing_reification σ Γ e τ φ → closed_at e Γ.length :=
  by
  intros σ Γ e τ φ Hτ
  cases Hτ <;> (apply typing.closed_at_env; assumption)

lemma typing.wf : ∀ σ Γ 𝕊 e τ φ, typing σ Γ 𝕊 e τ φ → wf_at e Γ.length :=
  by
  intros σ Γ 𝕊 e τ φ Hτ
  constructor
  apply typing.regular; apply Hτ
  apply typing.closed_at_env; apply Hτ

lemma typing_reification.wf : ∀ σ Γ e τ φ, typing_reification σ Γ e τ φ → wf_at e Γ.length :=
  by
  intros σ Γ e τ φ Hτ
  cases Hτ <;> (apply typing.wf; assumption)

lemma typing.dynamic_impl_wbt : ∀ σ Γ e τ φ, typing σ Γ 𝟚 e τ φ → wbt 𝟚 τ ∧ wbt_effects 𝟚 φ :=
  by
  generalize HEq𝕊 : 𝟚 = 𝕊
  intros σ Γ e τ φ Hτ
  revert HEq𝕊
  apply @typing.rec σ
    (fun Γ 𝕊 e τ φ (H : typing σ Γ 𝕊 e τ φ) => 𝟚 = 𝕊 → wbt 𝕊 τ ∧ wbt_effects 𝕊 φ)
    (fun Γ e τ φ (H : typing_reification σ Γ e τ φ) => true)
  <;> intros
  <;> (try assumption)
  <;> (try contradiction)
  case fvar x _ Hbinds Hwbt HEq𝕊 =>
    constructor; apply Hwbt; simp
  case lam Hwbt₀ Hclose IH HEq𝕊 =>
    have ⟨Hwbt₁, Hφ₀⟩ := IH HEq𝕊
    rw [← HEq𝕊]
    rw [← HEq𝕊] at Hwbt₀ Hwbt₁ Hφ₀
    constructor
    . constructor; apply Hφ₀
      constructor; apply Hwbt₀; apply Hwbt₁
    . simp
  case app₁ IHf IHarg HEq𝕊 =>
    have ⟨Hwbt₁, Hφ₁⟩ := IHf HEq𝕊
    have ⟨Hwbt₂, Hφ₂⟩ := IHarg HEq𝕊
    rw [← HEq𝕊]
    rw [← HEq𝕊] at Hwbt₁ Hwbt₂ Hφ₁ Hφ₂
    constructor
    . apply Hwbt₁.right.right
    . simp only [wbt_effects.union]
      constructor; constructor
      . apply Hwbt₁.left
      . apply Hφ₁
      . apply Hφ₂
  case lit HEq𝕊 =>
    rw [← HEq𝕊]
    constructor
    . simp
    . simp
  case lets Hwbt Hclose IHb IHe HEq𝕊 =>
    have ⟨Hwbt₀, Hφ₀⟩ := IHb HEq𝕊
    have ⟨Hwbt₁, Hφ₁⟩ := IHe HEq𝕊
    constructor
    . apply Hwbt₁
    . simp only [wbt_effects.union]
      constructor
      . apply Hφ₀
      . apply Hφ₁
  case unit HEq𝕊 =>
    rw [← HEq𝕊]
    constructor
    . simp
    . simp
  case load₁ IH HEq𝕊 =>
    have ⟨Hwbt, Hφ⟩ := IH HEq𝕊
    rw [← HEq𝕊]
    rw [← HEq𝕊] at Hφ
    constructor
    . simp
    . simp only [wbt_effects.union]
      constructor
      . apply Hφ
      . simp
  case alloc₁ IH HEq𝕊 =>
    have ⟨Hwbt, Hφ⟩ := IH HEq𝕊
    rw [← HEq𝕊]
    rw [← HEq𝕊] at Hφ
    constructor
    . simp
    . simp only [wbt_effects.union]
      constructor
      . apply Hφ
      . simp
  case store₁ IHl IHr HEq𝕊 =>
    have ⟨Hwbt₀, Hφ₀⟩ := IHl HEq𝕊
    have ⟨Hwbt₁, Hφ₁⟩ := IHr HEq𝕊
    rw [← HEq𝕊]
    rw [← HEq𝕊] at Hφ₀ Hφ₁
    constructor
    . simp
    . simp only [wbt_effects.union]
      constructor; constructor
      . apply Hφ₀
      . apply Hφ₁
      . simp
  case pure => simp
  case reify => simp

lemma typing.dynamic_impl_grounded : ∀ σ Γ e τ φ, typing σ Γ 𝟚 e τ φ → grounded e :=
  by
  generalize HEq𝕊 : 𝟚 = 𝕊
  intros σ Γ e τ φ Hτ
  revert HEq𝕊
  apply @typing.rec σ
    (fun Γ 𝕊 e τ φ (H : typing σ Γ 𝕊 e τ φ) => 𝟚 = 𝕊 → grounded e)
    (fun Γ e τ φ (H : typing_reification σ Γ e τ φ) => true)
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

lemma typing.dynamic_impl_loc_free : ∀ σ Γ e τ φ, typing σ Γ 𝟚 e τ φ → typing ϵ Γ 𝟚 e τ φ :=
  by
  generalize HEq𝕊 : 𝟚 = 𝕊
  intros σ Γ e τ φ Hτ
  revert HEq𝕊
  apply @typing.rec σ
    (fun Γ 𝕊 e τ φ (H : typing σ Γ 𝕊 e τ φ) => 𝟚 = 𝕊 → typing ϵ Γ 𝕊 e τ φ)
    (fun Γ e τ φ (H : typing_reification σ Γ e τ φ) => true)
  <;> intros
  <;> (try contradiction)
  case fvar Hbinds Hwbt HEq𝕊 =>
    apply typing.fvar
    apply Hbinds; apply Hwbt
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
