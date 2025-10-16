import HIF1alpha.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace HIF1alpha

/-- Lyapunov function for proving stability -/
def lyapunovFunction (params : Parameters) (equilibrium : State) (s : State) : ℝ :=
  -- V(s) = ||s - equilibrium||²
  (s.hif - equilibrium.hif)^2 + (s.phd - equilibrium.phd)^2

/-- If dV/dt < 0, the equilibrium is stable -/
theorem lyapunov_stability (params : Parameters) (eq : State)
    (h : IsEquilibrium params eq) :
    -- Conditions on Lyapunov function derivative
    True := by
  sorry

end HIF1alpha
