import CollapsingTowers.TwoLevelRec.Syntax.Defs

inductive value : Expr → Prop where
  | lam : ∀ e, lc (.lam e) → value (.lam e)
  | lit : ∀ n, value (.lit n)
  | code : ∀ e, lc e → value (.code e)

lemma lc.value : ∀ e, value e → lc e := by
  intro e Hvalue
  cases Hvalue with
  | lam _ Hclosed => apply Hclosed
  | lit => constructor
  | code _ Hclosed => apply Hclosed
