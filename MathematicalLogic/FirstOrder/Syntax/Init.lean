import Lean.Meta.Tactic.Simp.RegisterCommand

namespace FirstOrder

open Lean.Parser.Tactic

-- Thanks, lean-by-example!

/-- The `simp_syntax` attribute registers simp lemmas for FOL syntax. -/
register_simp_attr syntax_simp

/-- `syntax_simp` is a non-terminal tactic to simplify FOL syntax. It is a macro of
  `simp only [syntax_simp]`. -/
syntax "syntax_simp" (simpArgs)? (location)? : tactic

macro_rules
| `(tactic| syntax_simp $[[$args,*]]? $[at $loc]?) =>
  let args := args.map (·.getElems) |>.getD #[]
  `(tactic| simp only [syntax_simp, $args,*] $[at $loc]?)

end FirstOrder
