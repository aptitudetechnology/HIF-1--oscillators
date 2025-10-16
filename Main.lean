import HIF1alpha

def main : IO Unit := do
  IO.println "HIF-1α Oscillator Formalization Demo"
  IO.println "====================================="

  -- Example parameters
  let params : HIF1alpha.Parameters := {
    k1 := 1.0,
    k2 := 0.1,
    k3 := 0.05,
    k4 := 0.2,
    k5 := 0.1,
    k1_pos := by norm_num,
    k2_pos := by norm_num,
    k3_pos := by norm_num,
    k4_pos := by norm_num,
    k5_pos := by norm_num
  }

  IO.println s!"Parameters: {params}"

  -- Example state
  let state : HIF1alpha.State := { hif := 2.0, phd := 1.5 }
  IO.println s!"Initial state: {state}"

  -- Compute vector field
  let vf := HIF1alpha.vectorField params state
  IO.println s!"Vector field at state: {vf}"

  -- Check if equilibrium
  let is_eq := HIF1alpha.IsEquilibrium params state
  IO.println s!"Is equilibrium: {is_eq}"

  -- Example Lyapunov function
  let lyap := HIF1alpha.lyapunovFunction params state state
  IO.println s!"Lyapunov function at equilibrium: {lyap}"

  IO.println "Demo completed."
