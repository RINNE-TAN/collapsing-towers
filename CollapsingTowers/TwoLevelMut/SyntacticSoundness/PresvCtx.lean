import CollapsingTowers.TwoLevelMut.SyntacticTyping.Defs

lemma preservation.under_ctx𝔹 :
  ∀ Γ B e₀ τ φ,
    ctx𝔹 B →
    typing Γ 𝟙 B⟦e₀⟧ τ φ →
    ∃ τ𝕖 φ₀ φ𝔹,
      φ = φ₀ ∪ φ𝔹 ∧
      typing Γ 𝟙 e₀ τ𝕖 φ₀ ∧
      ∀ Δ e₁ φ₁,
        typing (Δ ++ Γ) 𝟙 e₁ τ𝕖 φ₁ →
        typing (Δ ++ Γ) 𝟙 B⟦e₁⟧ τ (φ₁ ∪ φ𝔹) :=
  by
  intros Γ B e₀ τ φ HB Hτ
  cases HB
  <;> try contradiction
  case appl₁ =>
    cases Hτ
    case app₁ τ𝕒 φ₀ φ₁ φ₂ Harg HX =>
      exists τ𝕒.arrow τ φ₀, φ₁, (φ₀ ∪ φ₂)
      constructor; cases φ₀ <;> cases φ₁ <;> cases φ₂ <;> simp
      constructor; apply HX
      intros Δ e₁ φ HX
      have HEqφ : φ ∪ (φ₀ ∪ φ₂) = φ₀ ∪ φ ∪ φ₂ := by cases φ₀ <;> cases φ₂ <;> simp
      rw [HEqφ]
      apply typing.app₁
      . apply HX
      . apply typing.weakening _ _ _ _ _ _ Harg
  case appr₁ =>
    cases Hτ
    case app₁ τ𝕒 φ₀ φ₁ φ₂ HX Hf =>
      exists τ𝕒, φ₂, (φ₀ ∪ φ₁)
      constructor; cases φ₀ <;> cases φ₁ <;> cases φ₂ <;> simp
      constructor; apply HX
      intros Δ e₁ φ HX
      have HEqφ : φ ∪ (φ₀ ∪ φ₁) = φ₀ ∪ φ₁ ∪ φ := by cases φ₀ <;> cases φ₁ <;> simp
      rw [HEqφ]
      apply typing.app₁
      . apply typing.weakening _ _ _ _ _ _ Hf
      . apply HX
  case appl₂ =>
    cases Hτ
    case app₂ τ𝕒 τ𝕓 φ₀ φ₁ HX Harg =>
      exists .fragment (.arrow τ𝕒 τ𝕓 ⊥), φ₀, ⊤
      constructor; simp
      constructor; apply HX
      intros Δ e₁ φ HX; simp
      apply typing.app₂
      . apply HX
      . apply typing.weakening _ _ _ _ _ _ Harg
  case appr₂ =>
    cases Hτ
    case app₂ τ𝕒 τ𝕓 φ₀ φ₁ Hf HX =>
      exists .fragment τ𝕒, φ₁, ⊤
      constructor; simp
      constructor; apply HX
      intros Δ e₁ φ HX; simp
      apply typing.app₂
      . apply typing.weakening _ _ _ _ _ _ Hf
      . apply HX
  case lift =>
    cases Hτ
    case lift_lam τ𝕒 τ𝕓 φ₀ φ₁ HX =>
      exists .arrow (.fragment τ𝕒) (.fragment τ𝕓) φ₀, φ₁, ⊤
      constructor; simp
      constructor; apply HX
      intros Δ e₁ φ HX; simp
      apply typing.lift_lam; apply HX
    case lift_lit φ₀ HX =>
      exists .nat, φ₀, ⊤
      constructor; simp
      constructor; apply HX
      intros Δ e₁ φ HX; simp
      apply typing.lift_lit; apply HX
    case lift_unit φ₀ HX =>
      exists .unit, φ₀, ⊤
      constructor; simp
      constructor; apply HX
      intros Δ e₁ φ HX; simp
      apply typing.lift_unit; apply HX
  case lets e Hlc =>
    cases Hτ
    case lets τ𝕒 φ₀ φ₁ Hwbt HX Hclosed He =>
      exists τ𝕒, φ₀, φ₁
      constructor; simp
      constructor; apply HX
      intros Δ e₁ φ HX
      apply typing.lets
      . apply HX
      . have HEq : ({0 ↦ (Δ ++ Γ).length}e) = (shiftl Γ.length Δ.length {0 ↦ Γ.length}e) :=
          by simp [comm.shiftl_opening, identity.shiftl _ _ _ Hclosed, Nat.add_comm]
        rw [HEq]
        apply typing.weakening.strengthened _ [(τ𝕒, 𝟙)] _ _ _ _ _ _ He (by simp)
      . apply Hwbt
      . apply closed.inc; apply Hclosed; simp
  case alloc₂ =>
    cases Hτ
    case alloc₂ φ HX =>
      exists .fragment .nat, φ, ⊤
      constructor; simp
      constructor; apply HX
      intros Δ e₁ φ HX; simp
      apply typing.alloc₂
      apply HX
  case load₂ =>
    cases Hτ
    case load₂ φ HX =>
      exists .fragment (.ref .nat), φ, ⊤
      constructor; simp
      constructor; apply HX
      intros Δ e₁ φ HX; simp
      apply typing.load₂
      apply HX
  case storel₂ =>
    cases Hτ
    case store₂ φ₀ φ₁ HX Hr =>
      exists .fragment (.ref .nat), φ₀, ⊤
      constructor; simp
      constructor; apply HX
      intros Δ e₁ φ HX; simp
      apply typing.store₂
      . apply HX
      . apply typing.weakening _ _ _ _ _ _ Hr
  case storer₂ =>
    cases Hτ
    case store₂ φ₀ φ₁ Hl HX =>
      exists .fragment .nat, φ₁, ⊤
      constructor; simp
      constructor; apply HX
      intros Δ e₁ φ HX; simp
      apply typing.store₂
      . apply typing.weakening _ _ _ _ _ _ Hl
      . apply HX

lemma preservation.under_ctxℝ :
  ∀ intro Γ R e₀ τ φ,
    ctxℝ intro Γ.length R →
    lc e₀ →
    typing Γ 𝟙 R⟦e₀⟧ τ φ →
    ∃ Δ τ𝕖 φ₀,
      Δ.length = Γ.length + intro ∧
      typing_reification Δ e₀ τ𝕖 φ₀ ∧
      ∀ e₁ φ₁,
        (store_free e₀ → store_free e₁) →
        fv e₁ ⊆ fv e₀ →
        typing_reification Δ e₁ τ𝕖 φ₁ →
        typing Γ 𝟙 R⟦e₁⟧ τ φ :=
  by
  intros intro Γ R e₀ τ φ HR Hlc Hτ
  cases HR
  case lam𝕔 =>
    cases Hτ
    case lam𝕔 τ𝕒 τ𝕓 φ₀ Hwbt HX Hclosed =>
      rw [identity.opening_closing _ _ _ Hlc] at HX
      exists (τ𝕒, 𝟚) :: Γ, .rep τ𝕓, φ₀
      constructor; simp
      constructor; apply HX
      intros e₁ φ₁ IHsf Hfv HX
      apply typing.lam𝕔
      . rw [identity.opening_closing _ _ _ (typing_reification.regular _ _ _ _ HX)]
        apply HX
      . apply Hwbt
      . rw [← closed.under_closing]
        apply typing_reification.closed_at_env _ _ _ _ HX
  case lets𝕔 =>
    cases Hτ
    case lets𝕔 τ𝕒 τ𝕓 φ₀ Hwbt Hb HX Hclosed =>
      rw [identity.opening_closing _ _ _ Hlc] at HX
      exists (τ𝕒, 𝟚) :: Γ, .rep τ𝕓, φ₀
      constructor; simp
      constructor; apply HX
      intros e₁ φ₁ IHsf Hfv HX
      apply typing.lets𝕔
      . apply Hb
      . rw [identity.opening_closing _ _ _ (typing_reification.regular _ _ _ _ HX)]
        apply HX
      . apply Hwbt
      . rw [← closed.under_closing]
        apply typing_reification.closed_at_env _ _ _ _ HX
  case run =>
    cases Hτ
    case run φ₀ Hsf Hclosed HX =>
      exists Γ, .rep τ, φ₀
      constructor; simp
      constructor; apply HX
      intros e₁ φ₁ IHsf Hfv HX
      apply typing.run
      . apply HX
      . apply IHsf Hsf
      . rw [closed_iff_fv_empty] at Hclosed
        simp [Hclosed] at Hfv
        rw [closed_iff_fv_empty, Hfv]

lemma preservation.under_ctx𝔼 :
  ∀ Γ E e₀ τ φ₀,
    ctx𝔼 E →
    typing Γ 𝟙 E⟦e₀⟧ τ φ₀ →
    ∃ τ𝕖 φ𝕖 φ𝔼,
      φ₀ = φ𝕖 ∪ φ𝔼 ∧
      typing Γ 𝟙 e₀ τ𝕖 φ𝕖 ∧
      ∀ Δ e₁ φ₁,
        typing (Δ ++ Γ) 𝟙 e₁ τ𝕖 φ₁ →
        typing (Δ ++ Γ) 𝟙 E⟦e₁⟧ τ (φ₁ ∪ φ𝔼) :=
  by
  intros Γ E e₀ τ φ₀ HE Hτ
  induction HE generalizing τ φ₀
  case hole =>
    exists τ, φ₀, ⊥
    constructor; cases φ₀ <;> rfl
    constructor; apply Hτ
    intros Δ e φ; simp
  case cons𝔹 B E HB HE IH =>
    have ⟨τ𝕖, φ₀, φ₁, HEqφ₀, Hτ, IHτB⟩ := preservation.under_ctx𝔹 _ _ _ _ _ HB Hτ
    have ⟨τ𝕖, φ₂, φ₃, HEqφ₁, Hτ, IHτE⟩ := IH _ _ Hτ
    rw [HEqφ₀, HEqφ₁]
    exists τ𝕖, φ₂, φ₁ ∪ φ₃
    constructor; cases φ₀ <;> cases φ₁ <;> cases φ₂ <;> cases φ₃ <;> simp
    constructor; apply Hτ
    intros Δ e φ Hτ
    have Hτ := IHτE _ _ _ Hτ
    have Hτ := IHτB _ _ _ Hτ
    have HEqφ : φ ∪ (φ₁ ∪ φ₃) = φ ∪ φ₃ ∪ φ₁ := by cases φ₁ <;> cases φ₃ <;> simp
    rw [HEqφ]; apply Hτ
