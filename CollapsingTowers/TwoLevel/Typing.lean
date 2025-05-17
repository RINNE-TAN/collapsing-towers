
import CollapsingTowers.TwoLevel.Shift
import CollapsingTowers.TwoLevel.SmallStep
import CollapsingTowers.TwoLevel.Env
@[simp]
def binds (x : ℕ) (τ : Ty) (Γ : TEnv) :=
  indexr x Γ = some τ

theorem binds_extend : ∀ Γ Δ x τ, binds x τ Γ -> binds x τ (Δ ++ Γ) :=
  by
  intros Γ Δ x τ Hbinds
  induction Δ with
  | nil => apply Hbinds
  | cons head tails IHtails =>
    simp
    by_cases Hx : tails.length + Γ.length = x
    . have Hx : x < Γ.length := by apply indexrSome'; exists τ
      omega
    . rw [if_neg Hx]; apply IHtails

theorem binds_extendr : ∀ Γ Δ x τ, binds x τ Γ -> binds (x + Δ.length) τ (Γ ++ Δ) :=
  by
  intros Γ Δ x τ
  induction Γ with
  | nil => simp
  | cons head tails IHtails =>
    simp
    by_cases HEq : tails.length = x
    . repeat rw [if_pos HEq]; simp
    . repeat rw [if_neg HEq]
      apply IHtails

theorem binds_shrink : ∀ Γ Δ x τ, x < Γ.length -> binds x τ (Δ ++ Γ) -> binds x τ Γ :=
  by
  intros Γ Δ x τ HLt
  induction Δ with
  | nil => simp
  | cons head tails IHtails =>
    intro Hbinds; apply IHtails
    simp at *
    have HNe : tails.length + Γ.length ≠ x := by omega
    rw [if_neg HNe] at Hbinds
    apply Hbinds

theorem binds_shrinkr : ∀ Γ Δ x τ, binds (x + Δ.length) τ (Γ ++ Δ) -> binds x τ Γ :=
  by
  intros Γ Δ x τ
  induction Γ with
  | nil =>
    simp; intro Hindexr
    have : x + Δ.length < Δ.length := by apply indexrSome'; exists τ
    omega
  | cons head tails IHtails =>
    simp
    by_cases HEq : tails.length = x
    . repeat rw [if_pos HEq]; simp
    . repeat rw [if_neg HEq]
      apply IHtails

inductive typing : TEnv -> Expr -> Ty -> Prop where
  | fvar : ∀ Γ x τ,
    binds x τ Γ ->
    typing Γ (.fvar x) τ
  | lam₁ : ∀ Γ e τ𝕒 τ𝕓,
    typing (τ𝕒 :: Γ) (open₀ Γ.length e) τ𝕓 ->
    closed_at e Γ.length ->
    typing Γ (.lam₁ e) (.arrow τ𝕒 τ𝕓)
  | lam₂ : ∀ Γ e τ𝕒 τ𝕓,
    typing Γ e (.arrow (.rep τ𝕒) (.rep τ𝕓)) ->
    typing Γ (.lam₂ e) (.rep (.arrow τ𝕒 τ𝕓))
  | app₁ : ∀ Γ f arg τ𝕒 τ𝕓,
    typing Γ f (.arrow τ𝕒 τ𝕓) ->
    typing Γ arg τ𝕒 ->
    typing Γ (.app₁ f arg) τ𝕓
  | app₂ : ∀ Γ f arg τ𝕒 τ𝕓,
    typing Γ f (.rep (.arrow τ𝕒 τ𝕓)) ->
    typing Γ arg (.rep τ𝕒) ->
    typing Γ (.app₂ f arg) (.rep τ𝕓)
  | plus₁ : ∀ Γ l r,
    typing Γ l .nat ->
    typing Γ r .nat ->
    typing Γ (.plus₁ l r) .nat
  | plus₂ : ∀ Γ l r,
    typing Γ l (.rep .nat) ->
    typing Γ r (.rep .nat) ->
    typing Γ (.plus₂ l r) (.rep .nat)
  | lit₁ : ∀ Γ n,
    typing Γ (.lit₁ n) .nat
  | lit₂ : ∀ Γ n,
    typing Γ n .nat ->
    typing Γ (.lit₂ n) (.rep .nat)
  | code : ∀ Γ e τ,
    typing Γ e τ ->
    typing Γ (.code e) (.rep τ)
  | reflect : ∀ Γ e τ,
    typing Γ e τ ->
    typing Γ (.reflect e) (.rep τ)
  | lam𝕔 : ∀ Γ e τ𝕒 τ𝕓,
    typing (τ𝕒 :: Γ) (open₀ Γ.length e) (.rep τ𝕓) ->
    closed_at e Γ.length ->
    neutral_lc e ->
    typing Γ (.lam𝕔 e) (.rep (.arrow τ𝕒 τ𝕓))
  | lets : ∀ Γ b e τ𝕒 τ𝕓,
    typing Γ b τ𝕒 ->
    typing (τ𝕒 :: Γ) (open₀ Γ.length e) τ𝕓 ->
    closed_at e Γ.length ->
    typing Γ (.lets b e) τ𝕓
  | let𝕔 : ∀ Γ b e τ𝕒 τ𝕓,
    typing Γ b τ𝕒 ->
    typing (τ𝕒 :: Γ) (open₀ Γ.length e) τ𝕓 ->
    closed_at e Γ.length ->
    neutral_lc e ->
    typing Γ (.let𝕔 b e) τ𝕓

example : typing [] expr₀ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₀, x₀]
  repeat constructor

example : typing [] expr₁ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₁, x₀]
  repeat constructor

example : typing [] expr₂ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₂, x₀]
  repeat constructor

example : typing [] expr₃ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₃, x₀, x₁]
  repeat constructor

example : typing [] expr₄ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₄, x₀, x₁]
  repeat constructor

example : typing [] expr₅ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₅, x₀, x₁, x₂]
  repeat constructor

example : typing [] expr₆ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₆, x₀, x₁, x₂]
  repeat constructor

example : typing [] expr₇ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₇, x₀, x₁, x₂]
  repeat constructor

example : typing [] expr₈ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₈, x₀, x₁, x₂]
  repeat constructor

example : typing [] expr₉ (.rep (.arrow .nat .nat)) :=
  by
  rw [expr₉, x₀, x₁, x₂]
  repeat constructor

example : typing [] expr𝕩 (.rep (.arrow .nat .nat)) :=
  by
  rw [expr𝕩, x₀, x₁, x₂]
  repeat constructor

theorem typing_regular : ∀ Γ e τ, typing Γ e τ -> lc e :=
  by
  intros Γ e τ Htyping
  induction Htyping with
  | fvar
  | lit₁=> constructor
  | lam₁ _ _ _ _ _ _ IHe
  | lam𝕔 _ _ _ _ _ _ _ IHe => apply open_closedb; apply IHe
  | app₁ _ _ _ _ _ _ _ IH₀ IH₁
  | app₂ _ _ _ _ _ _ _ IH₀ IH₁
  | plus₁ _ _ _ _ _ IH₀ IH₁
  | plus₂ _ _ _ _ _ IH₀ IH₁ => constructor; apply IH₀; apply IH₁
  | code _ _ _ _ IH
  | reflect _ _ _ _ IH
  | lit₂ _ _ _ IH
  | lam₂ _ _ _ _ _ IH => apply IH
  | lets _ _ _ _ _ _ _ _ IH₀ IH₁
  | let𝕔 _ _ _ _ _ _ _ _ _ IH₀ IH₁ => constructor; apply IH₀; apply open_closedb; apply IH₁

theorem typing_closed : ∀ Γ e τ, typing Γ e τ -> closed_at e Γ.length :=
  by
  intros Γ e τ Htyping
  induction Htyping with
  | fvar _ _ τ Hbind => simp at *; apply indexrSome'; exists τ
  | lam₁ _ _ _ _ _ IH
  | lam₂ _ _ _ _ _ IH
  | lam𝕔 _ _ _ _ _ IH
  | code _ _ _ _ IH
  | reflect _ _ _ _ IH
  | lit₂ _ _ _ IH => apply IH
  | app₁ _ _ _ _ _ _ _ IH₀ IH₁
  | app₂ _ _ _ _ _ _ _ IH₀ IH₁
  | plus₁ _ _ _ _ _ IH₀ IH₁
  | plus₂ _ _ _ _ _ IH₀ IH₁ => constructor; apply IH₀; apply IH₁
  | lets _ _ _ _ _ _ _ IH₀ IH₁
  | let𝕔 _ _ _ _ _ _ _ IH₀ _ IH₁ => constructor; apply IH₁; apply IH₀
  | lit₁ => constructor

theorem weakening_strengthened:
    ∀ Γ Ψ Δ Φ e τ, typing Γ e τ -> Γ = Ψ ++ Φ -> typing (Ψ ++ Δ ++ Φ) (shiftl_at Φ.length Δ.length e) τ :=
  by
  intros Γ Ψ Δ Φ e τ Hτ HEqΓ
  induction Hτ generalizing Ψ with
  | fvar _ x _ Hbinds =>
    rw [HEqΓ] at Hbinds
    by_cases HLe : Φ.length <= x
    . simp only [shiftl_at]; rw [if_pos HLe]; constructor
      rw [← Nat.add_sub_of_le HLe]
      rw [← Nat.add_sub_of_le HLe] at Hbinds
      rw [Nat.add_assoc, Nat.add_left_comm, ← Nat.add_assoc, Nat.add_right_comm]
      rw [Nat.add_comm] at Hbinds
      repeat apply binds_extendr
      apply binds_shrinkr; apply Hbinds
    . simp only [shiftl_at]; rw [if_neg HLe]; constructor
      apply binds_extend; apply binds_shrink
      omega; apply Hbinds
  | lam₁ _ _ _ _ _ Hclose IH =>
    rw [HEqΓ] at IH
    rw [HEqΓ] at Hclose
    rw [shiftl_open₀] at IH
    rw [List.length_append, Nat.add_right_comm] at IH
    constructor
    rw [← List.cons_append, ← List.cons_append, List.length_append, List.length_append]
    apply IH; rfl
    rw [List.length_append, List.length_append, Nat.add_right_comm]
    apply shiftl_closed_at; rw [← List.length_append]; apply Hclose
    simp
  | lam𝕔 _ _ _ _ _ Hclose HNeu IH =>
    rw [HEqΓ] at IH
    rw [HEqΓ] at Hclose
    rw [shiftl_open₀] at IH
    rw [List.length_append, Nat.add_right_comm] at IH
    constructor
    rw [← List.cons_append, ← List.cons_append, List.length_append, List.length_append]
    apply IH; rfl
    rw [List.length_append, List.length_append, Nat.add_right_comm]
    apply shiftl_closed_at; rw [← List.length_append]; apply Hclose
    apply shiftl_neutral_db; apply HNeu
    simp
  | app₁ _ _ _ _ _ _ _ IH₀ IH₁
  | app₂ _ _ _ _ _ _ _ IH₀ IH₁
  | plus₁ _ _ _ _ _ IH₀ IH₁
  | plus₂ _ _ _ _ _ IH₀ IH₁ =>
    constructor
    apply IH₀; apply HEqΓ
    apply IH₁; apply HEqΓ
  | lit₁ => constructor
  | code _ _ _ _ IH
  | reflect _ _ _ _ IH
  | lit₂ _ _ _ IH
  | lam₂ _ _ _ _ _ IH =>
    constructor; apply IH; apply HEqΓ
  | lets _ _ _ _ _ _ _ Hclose IHb IHe =>
    rw [HEqΓ] at IHe
    rw [HEqΓ] at Hclose
    rw [shiftl_open₀] at IHe
    rw [List.length_append, Nat.add_right_comm] at IHe
    constructor
    apply IHb; apply HEqΓ
    rw [← List.cons_append, ← List.cons_append, List.length_append, List.length_append]
    apply IHe; rfl
    rw [List.length_append, List.length_append, Nat.add_right_comm]
    apply shiftl_closed_at; rw [← List.length_append]; apply Hclose
    simp
  | let𝕔 _ _ _ _ _ _ _ Hclose HNeu IHb IHe =>
    rw [HEqΓ] at IHe
    rw [HEqΓ] at Hclose
    rw [shiftl_open₀] at IHe
    rw [List.length_append, Nat.add_right_comm] at IHe
    constructor
    apply IHb; apply HEqΓ
    rw [← List.cons_append, ← List.cons_append, List.length_append, List.length_append]
    apply IHe; rfl
    rw [List.length_append, List.length_append, Nat.add_right_comm]
    apply shiftl_closed_at; rw [← List.length_append]; apply Hclose
    apply shiftl_neutral_db; apply HNeu
    simp

theorem weakening : ∀ Γ Δ e τ, typing Γ e τ -> typing (Δ ++ Γ) e τ :=
  by
  intros Γ Δ e τ Hτ
  rw [← List.nil_append Δ]
  rw [← shiftl_id _ e]
  apply weakening_strengthened
  apply Hτ; rfl
  apply typing_closed; apply Hτ

theorem weakening1 : ∀ Γ e τ𝕒 τ𝕓, typing Γ e τ𝕓 -> typing (τ𝕒 :: Γ) e τ𝕓 :=
  by
  intros Γ e τ𝕒
  rw [← List.singleton_append]
  apply weakening

@[simp]
def typing_strengthened (Γ: TEnv) (e : Expr) (τ : Ty) : Prop :=
  neutral Γ.length e /\ typing Γ e τ

theorem typing_weakening_empty : ∀ e τ, typing [] e τ -> typing_strengthened [] e τ :=
  by
  intros e τ Hτ
  constructor
  apply closed_at_neutral; rw [← List.length_nil]
  apply typing_closed; apply Hτ
  apply Hτ
