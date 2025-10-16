import Lake
open Lake DSL

package «HIF1alphaOscillator» where
  -- add package configuration options here

lean_lib «HIF1alpha» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_exe «hif1alpha-oscillator» where
  root := `Main
