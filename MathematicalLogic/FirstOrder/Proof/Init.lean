import Mathlib.Tactic.Core

namespace FirstOrder.Language.Proof

open Lean Meta

initialize prwExt : SimpleScopedEnvExtension Name (Array Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun a n => a.push n
    initial := {}
  }

initialize registerBuiltinAttribute {
  name := `prw
  descr := "generalized congruence"
  add := fun decl _ kind ↦ MetaM.run' do
    prwExt.add decl kind
}

end FirstOrder.Language.Proof
