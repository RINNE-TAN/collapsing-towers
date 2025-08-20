import CollapsingTowers.TwoLevelRec.SyntacticTyping.Weakening
import CollapsingTowers.TwoLevelRec.OperationalSemantics.Defs

lemma preservation.under_ctx𝔹 :
  ∀ Γ B e₀ e₁ τ φ₀,
    ctx𝔹 B →
    (∀ τ φ₀,
      typing Γ 𝟚 e₀ τ φ₀ →
      ∃ φ₁,
        typing Γ 𝟚 e₁ τ φ₁ ∧
        φ₁ ≤ φ₀
    ) →
    typing Γ 𝟚 B⟦e₀⟧ τ φ₀ →
    ∃ φ₁,
      typing Γ 𝟚 B⟦e₁⟧ τ φ₁ ∧
      φ₁ ≤ φ₀ :=
  by
  intros Γ B e₀ e₁ τ φ₀ HB IH Hτ
  cases HB
  case appl₁ =>
    cases Hτ
    case app₁ φ₀ φ₁ φ₂ Harg HX =>
      have ⟨φₓ, HX, Hφ⟩ := IH _ _ HX
      exists φ₀ ∪ φₓ ∪ φ₂
      constructor
      . apply typing.app₁
        . apply HX
        . apply Harg
      . cases φ₀ <;> cases φ₁ <;> cases φ₂ <;> cases φₓ <;> simp at *
  case appr₁ =>
    cases Hτ
    case app₁ φ₀ φ₁ φ₂ HX Hf =>
      have ⟨φₓ, HX, Hφ⟩ := IH _ _ HX
      exists φ₀ ∪ φ₁ ∪ φₓ
      constructor
      . apply typing.app₁
        . apply Hf
        . apply HX
      . cases φ₀ <;> cases φ₁ <;> cases φ₂ <;> cases φₓ <;> simp at *
  case appl₂ =>
    cases Hτ
    case app₂ HX Harg =>
      have ⟨φₓ, HX, Hφ⟩ := IH _ _ HX
      exists ⊤
      constructor
      . apply typing.app₂
        . apply HX
        . apply Harg
      . simp
  case appr₂ =>
    cases Hτ
    case app₂ Hf HX =>
      have ⟨φₓ, HX, Hφ⟩ := IH _ _ HX
      exists ⊤
      constructor
      . apply typing.app₂
        . apply Hf
        . apply HX
      . simp
  case binaryl₁ =>
    cases Hτ
    case binary₁ φ₀ φ₁ HX Hr =>
      have ⟨φₓ, HX, Hφ⟩ := IH _ _ HX
      exists φₓ ∪ φ₁
      constructor
      . apply typing.binary₁
        . apply HX
        . apply Hr
      . cases φ₀ <;> cases φ₁ <;> cases φₓ <;> simp at *
  case binaryr₁ =>
    cases Hτ
    case binary₁ φ₀ φ₁ Hl HX =>
      have ⟨φₓ, HX, Hφ⟩ := IH _ _ HX
      exists φ₀ ∪ φₓ
      constructor
      . apply typing.binary₁
        . apply Hl
        . apply HX
      . cases φ₀ <;> cases φ₁ <;> cases φₓ <;> simp at *
  case binaryl₂ =>
    cases Hτ
    case binary₂ HX Hr =>
      have ⟨φₓ, HX, Hφ⟩ := IH _ _ HX
      exists ⊤
      constructor
      . apply typing.binary₂
        . apply HX
        . apply Hr
      . simp
  case binaryr₂ =>
    cases Hτ
    case binary₂ Hl HX =>
      have ⟨φₓ, HX, Hφ⟩ := IH _ _ HX
      exists ⊤
      constructor
      . apply typing.binary₂
        . apply Hl
        . apply HX
      . simp
  case lift =>
    cases Hτ
    case lift_lam HX =>
      have ⟨φₓ, HX, Hφ⟩ := IH _ _ HX
      exists ⊤
      constructor
      . apply typing.lift_lam; apply HX
      . simp
    case lift_lit HX =>
      have ⟨φₓ, HX, Hφ⟩ := IH _ _ HX
      exists ⊤
      constructor
      . apply typing.lift_lit; apply HX
      . simp
  case lets =>
    cases Hτ
    case lets φ₀ φ₁ Hwbt HX Hclosed He =>
      have ⟨φₓ, HX, Hφ⟩ := IH _ _ HX
      exists φₓ ∪ φ₁
      constructor
      . apply typing.lets
        . apply HX
        . apply He
        . apply Hwbt
        . apply Hclosed
      . cases φ₀ <;> cases φ₁ <;> cases φₓ <;> simp at *
  case fix₁ =>
    cases Hτ
    case fix₁ Hfixφ HX =>
      have ⟨φₓ, HX, Hφ⟩ := IH _ _ HX
      exists φₓ
      constructor
      . apply typing.fix₁
        . apply Hfixφ
        . apply HX
      . apply Hφ
  case fix₂ =>
    cases Hτ
    case fix₂ HX =>
      have ⟨φₓ, HX, Hφ⟩ := IH _ _ HX
      exists ⊤
      constructor
      . apply typing.fix₂; apply HX
      . simp
  case ifz₁ =>
    cases Hτ
    case ifz₁ φ₀ φ₁ φ₂ HX Hl Hr =>
      have ⟨φₓ, HX, Hφ⟩ := IH _ _ HX
      exists φₓ ∪ φ₁ ∪ φ₂
      constructor
      . apply typing.ifz₁
        . apply HX
        . apply Hl
        . apply Hr
      . cases φ₀ <;> cases φ₁ <;> cases φ₂ <;> cases φₓ <;> simp at *
  case ifz₂ =>
    cases Hτ
    case ifz₂ HX Hl Hr =>
      have ⟨φₓ, HX, Hφ⟩ := IH _ _ HX
      exists ⊤
      constructor
      . apply typing.ifz₂
        . apply HX
        . apply Hl
        . apply Hr
      . simp
