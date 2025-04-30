
import Mathlib.Data.Finset.Basic
import CollapsingTowers.TwoLevel.Basic
import CollapsingTowers.TwoLevel.OpenClose
import CollapsingTowers.TwoLevel.SmallStep
import CollapsingTowers.TwoLevel.Env
import CollapsingTowers.TwoLevel.Typing

@[simp]
def valType : Expr → Ty → Prop
  | .lam₁ t2, .arrow τ1 τ2 =>
    ∀ v1, valType v1 τ1 ∧ lc v1 →
    ∃ v2, stepn (open_subst v1 t2) v2 ∧ valType v2 τ2
  | .lit₁ _, .nat => true
  | .code e, .rep τ =>
    ∃ v, stepn e v ∧ valType v τ
  | _, _ => false

@[simp]
def expType (e : Expr) (τ : Ty) : Prop :=
  ∃ v, stepn e v ∧ lc v ∧ valType v τ

@[simp]
def envType (Δ : VEnv) (Γ : TEnv) : Prop :=
  Δ.length = Γ.length ∧ ∀ τ x, binds x τ Γ → ∃ v, indexr x Δ = some v ∧ lc v ∧ valType v τ

theorem envType.empty : envType [] [] := by simp

theorem envType.extend : ∀ Δ Γ v τ,
  envType Δ Γ → lc v → valType v τ → envType (v :: Δ) (τ :: Γ) := by
  intros Δ Γ v τ henv hcl hv; simp; simp at henv
  apply And.intro
  . apply henv.1
  . intros τ1 x bd; rcases henv with ⟨hlen, h⟩
    by_cases hx : (x = Γ.length)
    . rw [hx] at bd; simp at bd; rw [hlen]; simp [hx]; rw [<- bd]; apply And.intro; assumption; assumption
    . rw [if_neg hx] at bd; rw [hlen]; rw [if_neg hx]
      apply h; assumption

theorem envType.closed : ∀ Δ Γ,
  envType Δ Γ → (∀ x t1, indexr x Δ = some t1 → lc t1) := by
  intros Δ Γ henv; rcases henv with ⟨hlen, h⟩; intros x t1 hidx
  have hx : (x < Δ.length) := by apply indexrSome'; exists t1
  rw [hlen] at hx; have hidx' := indexrSome Γ x hx
  rcases hidx' with ⟨τ, hidx'⟩
  have ⟨t2, hidx'', hval⟩  := h τ x hidx'
  rcases hval with ⟨hcl, _⟩; rw [hidx] at hidx''; cases hidx''; assumption

@[simp]
def substF (Δ : VEnv) (t : Expr) : Expr :=
  match t with
  | .bvar _ => t
  | .fvar x =>
    match indexr x Δ with
    | none => t
    | some t' => t'
  | .lam₁ t1 => .lam₁ (substF Δ t1)
  | .lam₂ t1 => .lam₂ (substF Δ t1)
  | .app₁ t11 t12 => .app₁ (substF Δ t11) (substF Δ t12)
  | .app₂ t11 t12 => .app₂ (substF Δ t11) (substF Δ t12)
  | .lit₁ _ => t
  | .lit₂ _ => t
  | .plus₁ t1 t2 => .plus₁ (substF Δ t1) (substF Δ t2)
  | .plus₂ t1 t2 => .plus₂ (substF Δ t1) (substF Δ t2)
  | .code t1 => .code (substF Δ t1)
  | .reflect t1 => .reflect (substF Δ t1)
  | .lam𝕔 t1 => .lam𝕔 (substF Δ t1)
  | .lets t1 t2 => .lets (substF Δ t1) (substF Δ t2)
  | .let𝕔 t1 t2 => .let𝕔 (substF Δ t1) (substF Δ t2)

@[simp]
def semType (Γ : TEnv) (t : Expr) (τ : Ty) : Prop :=
  ∀ Δ, lc t → envType Δ Γ → expType (substF Δ t) τ

lemma substF.closedb_at: ∀ t Δ n,
  (forall x t1, indexr x Δ = some t1 -> closedb_at t1 0) ->
  (closedb_at t n) -> (closedb_at (substF Δ t) n) := by
  intros t; induction t <;> intros E n hidx hcl <;> simp
  case bvar x => simp at hcl; assumption
  case fvar x =>
    generalize h : indexr x E = v
    cases v <;> simp
    case some v => apply closedb_inc; apply hidx; apply h; omega
  case lam₁ t ih
     | lam₂ t ih
     | code e1 ih
     | reflect e1 ih
     | lam𝕔 e1 ih =>
    apply ih; apply hidx; simp at hcl; assumption
  case app₁ t1 t2 ih1 ih2
     | app₂ t1 t2 ih1 ih2
     | plus₁ e1 e2 ih1 ih2
     | plus₂ e1 e2 ih1 ih2
     | lets e1 e2 ih1 ih2
     | let𝕔 e1 e2 ih1 ih2 =>
    rcases hcl with ⟨hcl1, hcl2⟩
    apply And.intro
    . apply ih1; assumption; assumption
    . apply ih2; assumption; assumption

-- compatibility lemmas

lemma semType.fvar: ∀ Γ x τ, binds x τ Γ → semType Γ (.fvar x) τ := by
  intros Γ x τ bd Δ hcl henv; simp;
  rcases henv with ⟨_, h⟩;
  have ⟨v, hrv, semv⟩ := h τ x bd;
  exists v; rw [hrv]; simp; constructor; constructor; apply semv

lemma semType.lam₁: ∀ Γ e τ1 τ2,
  semType (τ1 :: Γ) (open₀ Γ.length e) τ2 →
  Γ.length ∉ fv e ->
  semType Γ (.lam₁ e) (.arrow τ1 τ2) := by
  intros Γ e τ1 τ2 hsem hfr Δ hcl henv
  exists (substF Δ (.lam₁ e));
  constructor; apply stepn.refl
  constructor; sorry
  sorry

lemma semType.lam₂: ∀ Γ e τ1 τ2,
  semType (.rep τ1 :: Γ) (open₀ Γ.length e) τ2 →
  Γ.length ∉ fv e ->
  semType Γ (.lam₂ e) (.rep (.arrow τ1 τ2)) := by
  sorry
