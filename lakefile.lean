import Lake
open Lake DSL

package «mathematical-logic» where
  -- add any package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require importGraph from git
  "https://github.com/leanprover-community/import-graph.git" @ "main"

require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4.git" @ "main"

@[default_target]
lean_lib «MathematicalLogic» where
  -- add any library configuration options here
  -- leanOptions := #[
  --   ⟨`linter.style.longLine, true⟩,
  -- ]

lean_exe GodelSentence where
  root := `Exec.GodelSentence
