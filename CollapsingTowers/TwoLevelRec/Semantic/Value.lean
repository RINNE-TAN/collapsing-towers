import CollapsingTowers.TwoLevelRec.Syntax.Defs

inductive value : Expr → Prop where
  | fix : ∀ e, lc (.fix e) → value (.fix e)
  | lit : ∀ n, value (.lit n)
  | code : ∀ e, lc e → value (.code e)

lemma lc.value : ∀ e, value e → lc e := by
  intro e Hvalue
  cases Hvalue with
  | fix _ Hlc => apply Hlc
  | lit => constructor
  | code _ Hlc => apply Hlc
