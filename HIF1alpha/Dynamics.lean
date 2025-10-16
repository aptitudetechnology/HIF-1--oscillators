import HIF1alpha.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic

namespace HIF1alpha

/-- The Jacobian matrix at a state -/
def jacobian (params : Parameters) (s : State) : Matrix (Fin 2) (Fin 2) ℝ :=
  sorry

/-- Eigenvalues determine local stability -/
theorem stability_criterion (params : Parameters) (s : State)
    (h : IsEquilibrium params s) :
    (∀ λ, eigenvalue (jacobian params s) λ → λ.re < 0) →
    -- Then s is locally asymptotically stable
    True := by
  sorry

end HIF1alpha
