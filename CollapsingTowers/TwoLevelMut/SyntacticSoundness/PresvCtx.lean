import CollapsingTowers.TwoLevelMut.SyntacticTyping.Defs

lemma preservation.under_ctx𝔹 :
  ∀ σ₀ Γ B e₀ τ φ,
    ctx𝔹 B →
    typing σ₀ Γ 𝟙 B⟦e₀⟧ τ φ →
    ∃ τ𝕖 φ₀ φ𝔹,
      φ = φ₀ ∪ φ𝔹 ∧
      typing σ₀ Γ 𝟙 e₀ τ𝕖 φ₀ ∧
      ∀ σ₁ Δ e₁ φ₁,
        σ₀.length ≤ σ₁.length →
        typing σ₁ (Δ ++ Γ) 𝟙 e₁ τ𝕖 φ₁ →
        typing σ₁ (Δ ++ Γ) 𝟙 B⟦e₁⟧ τ (φ₁ ∪ φ𝔹) :=
  by
  intros σ₀ Γ B e₀ τ φ HB Hτ
  cases HB
  case appl₁ =>
    cases Hτ
    case app₁ τ𝕒 φ₀ φ₁ φ₂ Harg HX =>
      exists τ𝕒.arrow τ φ₀, φ₁, (φ₀ ∪ φ₂)
      constructor; cases φ₀ <;> cases φ₁ <;> cases φ₂ <;> simp
      constructor; apply HX
      intros σ₁ Δ e₁ φ Hσ HX
      have HEqφ : φ ∪ (φ₀ ∪ φ₂) = φ₀ ∪ φ ∪ φ₂ := by cases φ₀ <;> cases φ₂ <;> simp
      rw [HEqφ]
      apply typing.app₁
      . apply HX
      . apply typing.weakening.store _ _ _ _ _ _ _ Hσ
        apply typing.weakening _ _ _ _ _ _ _ Harg
  case appr₁ =>
    cases Hτ
    case app₁ τ𝕒 φ₀ φ₁ φ₂ HX Hf =>
      exists τ𝕒, φ₂, (φ₀ ∪ φ₁)
      constructor; cases φ₀ <;> cases φ₁ <;> cases φ₂ <;> simp
      constructor; apply HX
      intros σ₁ Δ e₁ φ Hσ HX
      have HEqφ : φ ∪ (φ₀ ∪ φ₁) = φ₀ ∪ φ₁ ∪ φ := by cases φ₀ <;> cases φ₁ <;> simp
      rw [HEqφ]
      apply typing.app₁
      . apply typing.weakening.store _ _ _ _ _ _ _ Hσ
        apply typing.weakening _ _ _ _ _ _ _ Hf
      . apply HX
  case appl₂ =>
    cases Hτ
    case app₂ τ𝕒 τ𝕓 φ₀ φ₁ HX Harg =>
      exists .fragment (.arrow τ𝕒 τ𝕓 ⊥), φ₀, ⊤
      constructor; simp
      constructor; apply HX
      intros σ₁ Δ e₁ φ Hσ HX; simp
      apply typing.app₂
      . apply HX
      . apply typing.weakening.store _ _ _ _ _ _ _ Hσ
        apply typing.weakening _ _ _ _ _ _ _ Harg
  case appr₂ =>
    cases Hτ
    case app₂ τ𝕒 τ𝕓 φ₀ φ₁ Hf HX =>
      exists .fragment τ𝕒, φ₁, ⊤
      constructor; simp
      constructor; apply HX
      intros σ₁ Δ e₁ φ Hσ HX; simp
      apply typing.app₂
      . apply typing.weakening.store _ _ _ _ _ _ _ Hσ
        apply typing.weakening _ _ _ _ _ _ _ Hf
      . apply HX
  case lift =>
    cases Hτ
    case lift_lam τ𝕒 τ𝕓 φ₀ φ₁ HX =>
      exists .arrow (.fragment τ𝕒) (.fragment τ𝕓) φ₀, φ₁, ⊤
      constructor; simp
      constructor; apply HX
      intros σ₁ Δ e₁ φ Hσ HX; simp
      apply typing.lift_lam; apply HX
    case lift_lit φ₀ HX =>
      exists .nat, φ₀, ⊤
      constructor; simp
      constructor; apply HX
      intros σ₁ Δ e₁ φ Hσ HX; simp
      apply typing.lift_lit; apply HX
  case lets e Hlc =>
    cases Hτ
    case lets τ𝕒 φ₀ φ₁ Hwbt HX Hclosed He =>
      exists τ𝕒, φ₀, φ₁
      constructor; simp
      constructor; apply HX
      intros σ₁ Δ e₁ φ Hσ HX
      apply typing.lets
      . apply HX
      . have HEq : ({0 ↦ (Δ ++ Γ).length}e) = (shiftl Γ.length Δ.length {0 ↦ Γ.length}e) :=
          by simp [comm.shiftl_opening, identity.shiftl _ _ _ Hclosed, Nat.add_comm]
        rw [HEq]
        apply typing.weakening.store _ _ _ _ _ _ _ Hσ
        apply typing.weakening.strengthened _ _ [(τ𝕒, 𝟙)] _ _ _ _ _ _ He (by simp)
      . apply Hwbt
      . apply closed.inc; apply Hclosed; simp
  case alloc₁ =>
    cases Hτ
    case alloc₁ HX =>
      exists .nat, φ, ⊥
      constructor; simp
      constructor; apply HX
      intros σ₁ Δ e₁ φ Hσ HX; simp
      apply typing.alloc₁
      apply HX
  case alloc₂ =>
    cases Hτ
    case alloc₂ φ HX =>
      exists .fragment .nat, φ, ⊤
      constructor; simp
      constructor; apply HX
      intros σ₁ Δ e₁ φ Hσ HX; simp
      apply typing.alloc₂
      apply HX
  case load₁ =>
    cases Hτ
    case load₁ HX =>
      exists .ref .nat, φ, ⊥
      constructor; simp
      constructor; apply HX
      intros σ₁ Δ e₁ φ Hσ HX; simp
      apply typing.load₁
      apply HX
  case load₂ =>
    cases Hτ
    case load₂ φ HX =>
      exists .fragment (.ref .nat), φ, ⊤
      constructor; simp
      constructor; apply HX
      intros σ₁ Δ e₁ φ Hσ HX; simp
      apply typing.load₂
      apply HX
  case storel₁ =>
    cases Hτ
    case store₁ φ₀ φ₁ HX Hr =>
      exists .ref .nat, φ₀, φ₁
      constructor; simp
      constructor; apply HX
      intros σ₁ Δ e₁ φ Hσ HX
      apply typing.store₁
      . apply HX
      . apply typing.weakening.store _ _ _ _ _ _ _ Hσ
        apply typing.weakening _ _ _ _ _ _ _ Hr
  case storer₁ =>
    cases Hτ
    case store₁ φ₀ φ₁ Hl HX =>
      exists .nat, φ₁, φ₀
      constructor; cases φ₀ <;> cases φ₁ <;> simp
      constructor; apply HX
      intros σ₁ Δ e₁ φ Hσ HX
      have HEqφ : φ ∪ φ₀ = φ₀ ∪ φ := by cases φ₀ <;> simp
      rw [HEqφ]
      apply typing.store₁
      . apply typing.weakening.store _ _ _ _ _ _ _ Hσ
        apply typing.weakening _ _ _ _ _ _ _ Hl
      . apply HX
  case storel₂ =>
    cases Hτ
    case store₂ φ₀ φ₁ HX Hr =>
      exists .fragment (.ref .nat), φ₀, ⊤
      constructor; simp
      constructor; apply HX
      intros σ₁ Δ e₁ φ Hσ HX; simp
      apply typing.store₂
      . apply HX
      . apply typing.weakening.store _ _ _ _ _ _ _ Hσ
        apply typing.weakening _ _ _ _ _ _ _ Hr
  case storer₂ =>
    cases Hτ
    case store₂ φ₀ φ₁ Hl HX =>
      exists .fragment .nat, φ₁, ⊤
      constructor; simp
      constructor; apply HX
      intros σ₁ Δ e₁ φ Hσ HX; simp
      apply typing.store₂
      . apply typing.weakening.store _ _ _ _ _ _ _ Hσ
        apply typing.weakening _ _ _ _ _ _ _ Hl
      . apply HX

lemma preservation.under_ctxℝ :
  ∀ σ₀ intro Γ R e₀ τ φ,
    ctxℝ intro Γ.length R →
    lc e₀ →
    typing σ₀ Γ 𝟙 R⟦e₀⟧ τ φ →
    ∃ Δ τ𝕖 φ₀,
      Δ.length = Γ.length + intro ∧
      typing_reification σ₀ Δ e₀ τ𝕖 φ₀ ∧
      ∀ σ₁ e₁ φ₁,
        σ₀.length ≤ σ₁.length →
        fv e₁ ⊆ fv e₀ →
        typing_reification σ₁ Δ e₁ τ𝕖 φ₁ →
        typing σ₁ Γ 𝟙 R⟦e₁⟧ τ φ :=
  by
  intros σ₀ intro Γ R e₀ τ φ HR Hlc Hτ
  cases HR
  case lam𝕔 =>
    cases Hτ
    case lam𝕔 τ𝕒 τ𝕓 φ₀ Hwbt HX Hclosed =>
      rw [identity.opening_closing _ _ _ Hlc] at HX
      exists (τ𝕒, 𝟚) :: Γ, .rep τ𝕓, φ₀
      constructor; simp
      constructor; apply HX
      intros σ₁ e₁ φ₁ Hσ Hfv HX
      apply typing.lam𝕔
      . rw [identity.opening_closing _ _ _ (typing_reification.regular _ _ _ _ _ HX)]
        apply HX
      . apply Hwbt
      . rw [← closed.under_closing]
        apply typing_reification.closed_at_env _ _ _ _ _ HX
  case lets𝕔 =>
    cases Hτ
    case lets𝕔 τ𝕒 τ𝕓 φ₀ Hwbt Hb HX Hclosed =>
      rw [identity.opening_closing _ _ _ Hlc] at HX
      exists (τ𝕒, 𝟚) :: Γ, .rep τ𝕓, φ₀
      constructor; simp
      constructor; apply HX
      intros σ₁ e₁ φ₁ Hσ Hfv HX
      apply typing.lets𝕔
      . apply typing.weakening.store _ _ _ _ _ _ _ Hσ Hb
      . rw [identity.opening_closing _ _ _ (typing_reification.regular _ _ _ _ _ HX)]
        apply HX
      . apply Hwbt
      . rw [← closed.under_closing]
        apply typing_reification.closed_at_env _ _ _ _ _ HX
  case run =>
    cases Hτ
    case run φ₀ Hclosed HX =>
      exists Γ, .rep τ, φ₀
      constructor; simp
      constructor; apply HX
      intros σ₁ e₁ φ₁ Hσ Hfv HX
      apply typing.run
      . apply HX
      . rw [closed_iff_fv_empty] at Hclosed
        simp [Hclosed] at Hfv
        rw [closed_iff_fv_empty, Hfv]

lemma preservation.under_ctx𝔼 :
  ∀ σ₀ Γ E e₀ τ φ₀,
    ctx𝔼 E →
    typing σ₀ Γ 𝟙 E⟦e₀⟧ τ φ₀ →
    ∃ τ𝕖 φ𝕖 φ𝔼,
      φ₀ = φ𝕖 ∪ φ𝔼 ∧
      typing σ₀ Γ 𝟙 e₀ τ𝕖 φ𝕖 ∧
      ∀ σ₁ Δ e₁ φ₁,
        σ₀.length ≤ σ₁.length →
        typing σ₁ (Δ ++ Γ) 𝟙 e₁ τ𝕖 φ₁ →
        typing σ₁ (Δ ++ Γ) 𝟙 E⟦e₁⟧ τ (φ₁ ∪ φ𝔼) :=
  by
  intros σ₀ Γ E e₀ τ φ₀ HE Hτ
  induction HE generalizing τ φ₀
  case hole =>
    exists τ, φ₀, ⊥
    constructor; cases φ₀ <;> rfl
    constructor; apply Hτ
    intros σ₁ Δ e φ Hσ; simp
  case cons𝔹 B E HB HE IH =>
    have ⟨τ𝕖, φ₀, φ₁, HEqφ₀, Hτ, IHτB⟩ := preservation.under_ctx𝔹 _ _ _ _ _ _ HB Hτ
    have ⟨τ𝕖, φ₂, φ₃, HEqφ₁, Hτ, IHτE⟩ := IH _ _ Hτ
    rw [HEqφ₀, HEqφ₁]
    exists τ𝕖, φ₂, φ₁ ∪ φ₃
    constructor; cases φ₀ <;> cases φ₁ <;> cases φ₂ <;> cases φ₃ <;> simp
    constructor; apply Hτ
    intros σ₁ Δ e φ Hσ Hτ
    have Hτ := IHτE _ _ _ _ Hσ Hτ
    have Hτ := IHτB _ _ _ _ Hσ Hτ
    have HEqφ : φ ∪ (φ₁ ∪ φ₃) = φ ∪ φ₃ ∪ φ₁ := by cases φ₁ <;> cases φ₃ <;> simp
    rw [HEqφ]; apply Hτ
