import Mathlib.Tactic.Core

namespace FirstOrder.Language.Proof.Tactic

open Lean Meta

initialize prwExt : SimpleScopedEnvExtension Name (Array Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun a n => a.push n
    initial := {}
  }

/-- Congruence theorems tagged with `@[prw]` attribute are used for `prw` tactic. -/
syntax (name := prwAttr) "prw" : attr

initialize registerBuiltinAttribute {
  name := `prwAttr
  descr := "prw congruence"
  add := fun decl _ kind ↦ MetaM.run' do
    prwExt.add decl kind
}

end FirstOrder.Language.Proof.Tactic
