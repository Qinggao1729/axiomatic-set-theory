import Lean

open Lean Meta

initialize setSpecSimpExt : SimpExtension ←
  registerSimpAttr `set_spec_simps "Set `*.Spec` simp lemmas"
