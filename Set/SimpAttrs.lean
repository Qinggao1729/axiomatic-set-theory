import Lean

/-- Set `*.Spec` simp lemmas. -/
register_simp_attr set_spec_simps

/-- Basic propositional simplification lemmas used in controlled `simp only`. -/
register_simp_attr prop_simps

/-- Non-`*.Spec` bridge lemmas for function-evaluation side conditions. -/
register_simp_attr function_eval_sideconds
