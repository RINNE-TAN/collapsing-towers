import CollapsingTowers.TwoLevelRec.OperationalSemantics.Defs
import CollapsingTowers.TwoLevelRec.SyntacticTyping.Defs

lemma preservation.reflect :
  ∀ Γ P E e τ φ,
    ctxℙ Γ.length P →
    ctx𝔼 E →
    lc e →
    typing Γ 𝟙 P⟦E⟦.reflect e⟧⟧ τ φ →
    typing Γ 𝟙 P⟦.lets𝕔 e E⟦.code (.bvar 0)⟧⟧ τ φ :=
  by
  intros Γ P E e τ φ HP HE Hlc Hτ
  admit
