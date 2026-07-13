import Instar.TwoLevelRec.SyntacticTyping.Defs

lemma preservation.under_ctx𝔹 :
  ∀ Γ B e₀ τ ε,
    ctx𝔹 B →
    typing Γ 𝟙 B⟦e₀⟧ τ ε →
    ∃ τ𝕖 ε₀ ε𝔹,
      ε = ε₀ ∪ ε𝔹 ∧
      typing Γ 𝟙 e₀ τ𝕖 ε₀ ∧
      ∀ Δ e₁ ε₁,
        typing (Δ ++ Γ) 𝟙 e₁ τ𝕖 ε₁ →
        typing (Δ ++ Γ) 𝟙 B⟦e₁⟧ τ (ε₁ ∪ ε𝔹) :=
  by
  intros Γ B e τ ε HB Hτ
  cases HB
  case appl₁ =>
    cases Hτ
    case app₁ τ𝕒 ε₀ ε₁ ε₂ Harg HX =>
      exists τ𝕒.arrow τ ε₀, ε₁, (ε₀ ∪ ε₂)
      constructor; cases ε₀ <;> cases ε₁ <;> cases ε₂ <;> simp
      constructor; apply HX
      intros Δ eₓ ε HX
      have HEqε : ε ∪ (ε₀ ∪ ε₂) = ε₀ ∪ ε ∪ ε₂ := by cases ε₀ <;> cases ε₂ <;> simp
      rw [HEqε]
      apply typing.app₁; apply HX; apply typing.weakening _ _ _ _ _ _ Harg
  case appr₁ =>
    cases Hτ
    case app₁ τ𝕒 ε₀ ε₁ ε₂ HX Hf =>
      exists τ𝕒, ε₂, (ε₀ ∪ ε₁)
      constructor; cases ε₀ <;> cases ε₁ <;> cases ε₂ <;> simp
      constructor; apply HX
      intros Δ eₓ ε HX
      have HEqε : ε ∪ (ε₀ ∪ ε₁) = ε₀ ∪ ε₁ ∪ ε := by cases ε₀ <;> cases ε₁ <;> simp
      rw [HEqε]
      apply typing.app₁; apply typing.weakening _ _ _ _ _ _ Hf; apply HX
  case appl₂ =>
    cases Hτ
    case app₂ τ𝕒 τ𝕓 ε₀ ε₁ HX Harg =>
      exists .fragment (.arrow τ𝕒 τ𝕓 ⊥), ε₀, ⊤
      constructor; simp
      constructor; apply HX
      intros Δ eₓ ε HX; simp
      apply typing.app₂; apply HX; apply typing.weakening _ _ _ _ _ _ Harg
  case appr₂ =>
    cases Hτ
    case app₂ τ𝕒 τ𝕓 ε₀ ε₁ Hf HX =>
      exists .fragment τ𝕒, ε₁, ⊤
      constructor; simp
      constructor; apply HX
      intros Δ eₓ ε HX; simp
      apply typing.app₂; apply typing.weakening _ _ _ _ _ _ Hf; apply HX
  case binaryl₁ =>
    cases Hτ
    case binary₁ ε₀ ε₁ HX Hr =>
      exists .nat, ε₀, ε₁
      constructor; simp
      constructor; apply HX
      intros Δ eₓ ε HX
      apply typing.binary₁; apply HX; apply typing.weakening _ _ _ _ _ _ Hr
  case binaryr₁ =>
    cases Hτ
    case binary₁ ε₀ ε₁ Hl HX =>
      exists .nat, ε₁, ε₀
      constructor; cases ε₀ <;> cases ε₁ <;> simp
      constructor; apply HX
      intros Δ eₓ ε HX
      have HEqε : ε ∪ ε₀ = ε₀ ∪ ε := by cases ε₀ <;> simp
      rw [HEqε]
      apply typing.binary₁; apply typing.weakening _ _ _ _ _ _ Hl; apply HX
  case binaryl₂ =>
    cases Hτ
    case binary₂ ε₀ ε₁ HX Hr =>
      exists (.fragment .nat), ε₀, ⊤
      constructor; simp
      constructor; apply HX
      intros Δ eₓ ε HX; simp
      apply typing.binary₂; apply HX; apply typing.weakening _ _ _ _ _ _ Hr
  case binaryr₂ =>
    cases Hτ
    case binary₂ ε₀ ε₁ Hl HX =>
      exists (.fragment .nat), ε₁, ⊤
      constructor; simp
      constructor; apply HX
      intros Δ eₓ ε HX; simp
      apply typing.binary₂; apply typing.weakening _ _ _ _ _ _ Hl; apply HX
  case lift =>
    cases Hτ
    case lift_lam τ𝕒 τ𝕓 ε₀ ε₁ HX =>
      exists .arrow (.fragment τ𝕒) (.fragment τ𝕓) ε₀, ε₁, ⊤
      constructor; simp
      constructor; apply HX
      intros Δ eₓ ε HX; simp
      apply typing.lift_lam; apply HX
    case lift_lit ε₀ HX =>
      exists .nat, ε₀, ⊤
      constructor; simp
      constructor; apply HX
      intros Δ eₓ ε HX; simp
      apply typing.lift_lit; apply HX
  case lets e Hlc =>
    cases Hτ
    case lets τ𝕒 ε₀ ε₁ Hwbt HX Hclosed He =>
      exists τ𝕒, ε₀, ε₁
      constructor; simp
      constructor; apply HX
      intros Δ eₓ ε HX
      apply typing.lets
      . apply HX
      . have HEq : ({0 ↦ (Δ ++ Γ).length}e) = (shiftl Γ.length Δ.length {0 ↦ Γ.length}e) :=
          by simp [comm.shiftl_opening, identity.shiftl _ _ _ Hclosed, Nat.add_comm]
        rw [HEq]
        apply typing.weakening.strengthened _ [(τ𝕒, 𝟙)] _ _ _ _ _ _ He (by simp)
      . apply Hwbt
      . apply closed.inc; apply Hclosed; simp
  case fix₁ =>
    cases Hτ
    case fix₁ τ𝕒 τ𝕓 ε₀ ε₁ Hfixε HX =>
      exists .arrow (.arrow τ𝕒 τ𝕓 ε₀) (.arrow τ𝕒 τ𝕓 ε₀) ε₁, ε, ⊥
      constructor; simp
      constructor; apply HX
      intros Δ eₓ ε HX; simp
      apply typing.fix₁; apply Hfixε; apply HX
  case fix₂ =>
    cases Hτ
    case fix₂ τ𝕒 τ𝕓 ε₀ HX =>
      exists .fragment (.arrow (.arrow τ𝕒 τ𝕓 ⊥) (.arrow τ𝕒 τ𝕓 ⊥) ⊥), ε₀, ⊤
      constructor; simp
      constructor; apply HX
      intros Δ eₓ ε HX; simp
      apply typing.fix₂; apply HX
  case ifz₁ =>
    cases Hτ
    case ifz₁ ε₀ ε₁ ε₂ HX Hl Hr =>
      exists .nat, ε₀, ε₁ ∪ ε₂
      constructor; cases ε₀ <;> cases ε₁ <;> cases ε₂ <;> simp
      constructor; apply HX
      intros Δ eₓ ε HX
      have HEqε : ε ∪ (ε₁ ∪ ε₂) = ε ∪ ε₁ ∪ ε₂ := by cases ε₁ <;> cases ε₂ <;> simp
      rw [HEqε]
      apply typing.ifz₁; apply HX; apply typing.weakening _ _ _ _ _ _ Hl; apply typing.weakening _ _ _ _ _ _ Hr
  case ifz₂ =>
    cases Hτ
    case ifz₂ ε₀ ε₁ ε₂ HX Hl Hr =>
      exists .fragment .nat, ε₀, ⊤
      constructor; simp
      constructor; apply HX
      intros Δ eₓ ε HX; simp
      apply typing.ifz₂; apply HX; apply typing_reification.weakening _ _ _ _ _ Hl; apply typing_reification.weakening _ _ _ _ _ Hr

lemma preservation.under_ctxℝ :
  ∀ intro Γ R e₀ τ ε,
    ctxℝ intro Γ.length R →
    lc e₀ →
    typing Γ 𝟙 R⟦e₀⟧ τ ε →
    ∃ Δ τ𝕖 ε₀,
      Δ.length = Γ.length + intro ∧
      typing_reification Δ e₀ τ𝕖 ε₀ ∧
      ∀ e₁ ε₁,
        fv e₁ ⊆ fv e₀ →
        typing_reification Δ e₁ τ𝕖 ε₁ →
        typing Γ 𝟙 R⟦e₁⟧ τ ε :=
  by
  intros intro Γ R e₀ τ ε HR Hlc Hτ
  cases HR
  case lam𝕔 =>
    cases Hτ
    case lam𝕔 τ𝕒 τ𝕓 ε₀ Hwbt HX Hclosed =>
      rw [identity.opening_closing _ _ _ Hlc] at HX
      exists (τ𝕒, 𝟚) :: Γ, .rep τ𝕓, ε₀
      constructor; simp
      constructor; apply HX
      intros e₁ ε₁ Hfv HX
      apply typing.lam𝕔
      . rw [identity.opening_closing _ _ _ (typing_reification.regular _ _ _ _ HX)]
        apply HX
      . apply Hwbt
      . rw [← closed.under_closing]
        apply typing_reification.closed_at_env _ _ _ _ HX
  case lets𝕔 =>
    cases Hτ
    case lets𝕔 τ𝕒 τ𝕓 ε₀ Hwbt Hb HX Hclosed =>
      rw [identity.opening_closing _ _ _ Hlc] at HX
      exists (τ𝕒, 𝟚) :: Γ, .rep τ𝕓, ε₀
      constructor; simp
      constructor; apply HX
      intros e₁ ε₁ Hfv HX
      apply typing.lets𝕔
      . apply Hb
      . rw [identity.opening_closing _ _ _ (typing_reification.regular _ _ _ _ HX)]
        apply HX
      . apply Hwbt
      . rw [← closed.under_closing]
        apply typing_reification.closed_at_env _ _ _ _ HX
  case run =>
    cases Hτ
    case run ε₀ Hclosed HX =>
      exists Γ, .rep τ, ε₀
      constructor; simp
      constructor; apply HX
      intros e₁ ε₁ Hfv HX
      apply typing.run
      . apply HX
      . rw [closed_iff_fv_empty] at Hclosed
        simp [Hclosed] at Hfv
        rw [closed_iff_fv_empty, Hfv]
  case ifzl₂ =>
    cases Hτ
    case ifz₂ τ ε₀ ε₁ ε₂ Hc HX Hr =>
      exists Γ, .rep τ, ε₁
      constructor; simp
      constructor; apply HX
      intros e₁ ε₁ Hfv HX
      apply typing.ifz₂
      . apply Hc
      . apply HX
      . apply Hr
  case ifzr₂ =>
    cases Hτ
    case ifz₂ τ ε₀ ε₁ ε₂ Hc Hl HX =>
      exists Γ, .rep τ, ε₂
      constructor; simp
      constructor; apply HX
      intros e₁ ε₁ Hfv HX
      apply typing.ifz₂
      . apply Hc
      . apply Hl
      . apply HX

lemma preservation.under_ctx𝔼 :
  ∀ Γ E e₀ τ ε₀,
    ctx𝔼 E →
    typing Γ 𝟙 E⟦e₀⟧ τ ε₀ →
    ∃ τ𝕖 ε𝕖 ε𝔼,
      ε₀ = ε𝕖 ∪ ε𝔼 ∧
      typing Γ 𝟙 e₀ τ𝕖 ε𝕖 ∧
      ∀ Δ e₁ ε₁,
        typing (Δ ++ Γ) 𝟙 e₁ τ𝕖 ε₁ →
        typing (Δ ++ Γ) 𝟙 E⟦e₁⟧ τ (ε₁ ∪ ε𝔼) :=
  by
  intros Γ E e τ ε HE Hτ
  induction HE generalizing τ ε
  case hole =>
    exists τ, ε, ⊥
    constructor; cases ε <;> rfl
    constructor; apply Hτ
    intros Δ e ε Hτ; simp; apply Hτ
  case cons𝔹 B E HB HE IH =>
    have ⟨τ𝕖, ε₀, ε₁, HEqε₀, Hτ, IHτB⟩ := preservation.under_ctx𝔹 _ _ _ _ _ HB Hτ
    have ⟨τ𝕖, ε₂, ε₃, HEqε₁, Hτ, IHτE⟩ := IH _ _ Hτ
    rw [HEqε₀, HEqε₁]
    exists τ𝕖, ε₂, ε₁ ∪ ε₃
    constructor; cases ε₀ <;> cases ε₁ <;> cases ε₂ <;> cases ε₃ <;> simp
    constructor; apply Hτ
    intros Δ e ε Hτ
    have Hτ := IHτE _ _ _ Hτ
    have Hτ := IHτB _ _ _ Hτ
    have HEqε : ε ∪ (ε₁ ∪ ε₃) = ε ∪ ε₃ ∪ ε₁ := by cases ε₁ <;> cases ε₃ <;> simp
    rw [HEqε]; apply Hτ
