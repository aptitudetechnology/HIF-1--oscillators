# Prompt for Proving HIF-1α Oscillator Placeholders in Lean 4

## Context

You are working with a Lean 4 formalization of HIF-1α oscillators, a biological system exhibiting periodic behavior. The codebase has placeholder theorems marked with `sorry` that need formal proofs. Your task is to provide complete, verified proofs using Lean 4 tactics and Mathlib4.

## System Description

The HIF-1α oscillator is modeled as a 2D ODE system:
- **dH/dt = k₁ - k₂·H·P - k₃·H** (HIF-1α dynamics)
- **dP/dt = k₄·H - k₅·P** (PHD enzyme dynamics)

Where all rate constants (k₁, k₂, k₃, k₄, k₅) are positive reals.

## Your Task

For each theorem below, provide:
1. **Strategy outline**: High-level proof approach
2. **Required lemmas**: Helper results you'll need (cite Mathlib if they exist)
3. **Complete proof**: Full Lean 4 tactic proof
4. **Alternative approaches**: If the direct proof is too hard, suggest workarounds

---

## Theorem 1: Existence and Uniqueness of Solutions

```lean
theorem solution_exists_unique (params : Parameters) (s₀ : State) 
    (h : s₀ ∈ StateSpace) :
    ∃! traj : Trajectory, 
      IsSolution params traj ∧ 
      traj 0 = s₀ ∧
      ∀ t, traj t ∈ StateSpace := by
  sorry
```

**Mathematical Background**: This is the Picard-Lindelöf theorem. The vector field is:
- Continuous (polynomials in H and P)
- Locally Lipschitz continuous
- The state space is invariant under the flow (positivity preserved)

**Proof Requirements**:
- Show the vector field `vectorField params` is Lipschitz continuous on compact sets
- Show the state space is forward-invariant (if H,P ≥ 0, then dH/dt and dP/dt preserve non-negativity at boundaries)
- Apply Mathlib's ODE existence theorem (look in `Mathlib.Analysis.ODE.Basic` or `Mathlib.Analysis.ODE.PicardLindelof`)
- Prove uniqueness follows from Lipschitz continuity

**Hints**:
- Check if `ODE.exists_forall_deriv_within_Icc_eq_of_lipschitzOnWith` or similar exists
- You may need to strengthen hypotheses (e.g., work on compact time intervals first)
- Consider using `DifferentiableOn` and `LipschitzOnWith`

---

## Theorem 2: Boundedness of Solutions

```lean
theorem solutions_bounded (params : Parameters) (traj : Trajectory)
    (h : IsSolution params traj) :
    ∃ M : ℝ, ∀ t : ℝ, 
      (traj t).hif ≤ M ∧ (traj t).phd ≤ M := by
  sorry
```

**Mathematical Background**: Use a priori estimates:
- From dH/dt equation: H is bounded by k₁/k₃ in the long run
- From dP/dt equation: P is bounded by (k₄/k₅) · max(H)

**Proof Strategy**:
1. Show dH/dt ≤ k₁ - k₃·H, which implies H ≤ k₁/k₃ + initial transient
2. Use this to bound dP/dt ≤ k₄·(k₁/k₃) - k₅·P
3. Conclude P is bounded
4. Take M = max of these bounds plus margin

**Required Lemmas**:
- Differential inequality comparison lemmas
- Properties of solutions to linear ODEs (for comparison functions)
- `max` and `sup` properties for bounds

**Hints**:
- May be easier to prove separately for H and P
- Use `Real.le_of_forall_le_of_dense` or similar
- Consider proving on finite intervals first, then take supremum

---

## Theorem 3: Existence of Equilibrium

```lean
theorem equilibrium_exists (params : Parameters) :
    ∃ s : State, IsEquilibrium params s ∧ s ∈ StateSpace := by
  sorry
```

**Mathematical Background**: Solve the system:
- 0 = k₁ - k₂·H·P - k₃·H
- 0 = k₄·H - k₅·P

From equation 2: P = (k₄/k₅)·H
Substitute into equation 1 and solve for H.

**Proof Strategy**:
1. Define H* = k₁/(k₃ + k₂·k₄/k₅) (solve algebraically)
2. Define P* = (k₄/k₅)·H*
3. Show (H*, P*) satisfies `vectorField params ⟨H*, P*⟩ = ⟨0, 0⟩`
4. Show H*, P* > 0 (using positivity of all parameters)

**Required Lemmas**:
- Field arithmetic in ℝ
- Division by positive numbers preserves positivity
- `mul_comm`, `div_mul_cancel`, etc.

**Hints**:
- Use `field_simp` tactic for algebraic manipulations
- `positivity` tactic for proving positivity
- `ring` or `ring_nf` for polynomial equalities

---

## Theorem 4: Limit Cycle Existence

```lean
theorem limit_cycle_exists (params : Parameters)
    (h_regime : params.k4 > params.k2 * params.k5 / params.k3)
    : ∃ lc : LimitCycle params, True := by
  sorry
```

**Mathematical Background**: This requires proving:
- The equilibrium becomes unstable when the condition holds (eigenvalues have positive real part)
- By Poincaré-Bendixson theorem (2D system, bounded trajectories, no equilibria or unstable equilibrium) ⟹ limit cycle exists

**Proof Strategy** (HARD - may need axioms):
1. Compute Jacobian at equilibrium
2. Show eigenvalues cross imaginary axis at the parameter threshold
3. Apply Poincaré-Bendixson (NOT IN MATHLIB - you'll need to axiomatize or cite)
4. Use boundedness theorem to ensure trajectories stay in compact region

**Status in Mathlib**: ❌ **Poincaré-Bendixson theorem is NOT formalized**

**Workarounds**:
- **Option A**: Add as axiom temporarily:
  ```lean
  axiom poincare_bendixson : [statement]
  ```
- **Option B**: Prove for specific parameter values using numerical verification
- **Option C**: State as admitted theorem and contribute to Mathlib later

**If proving from scratch**:
- This is a significant undertaking (weeks/months of work)
- Would be a major contribution to Mathlib
- Consider collaborating with Lean community

---

## Theorem 5: Critical Coupling for Kuramoto Synchronization

```lean
theorem critical_coupling_exists (n : ℕ) (params : Parameters) :
    ∃ K_c : ℝ, ∀ K > K_c, 
      -- Most initial conditions lead to synchronization
      True := by
  sorry
```

**Mathematical Background**: Kuramoto's theorem states:
- For identical oscillators: K_c = 0
- For heterogeneous oscillators: K_c depends on frequency distribution
- Above K_c, a bifurcation occurs where synchronized state becomes stable

**Proof Strategy** (VERY HARD):
1. Define the order parameter r(t) measuring synchronization
2. Show r satisfies a self-consistency equation
3. Prove bifurcation at critical coupling K_c
4. Show basin of attraction for synchronized state has positive measure for K > K_c

**Status in Mathlib**: ❌ **Kuramoto theory is NOT formalized**

**Recommended Approach**:
- Start with the **simplified case**: 2 identical oscillators
- Prove they synchronize for any K > 0
- This is tractable and illustrates the concept
- Extend to n identical oscillators (much easier than heterogeneous case)

---

## General Proof Tactics Toolkit

### For Real Number Arithmetic:
- `ring` / `ring_nf` - polynomial identities
- `field_simp` - simplify field expressions
- `norm_num` - numerical computation
- `positivity` - prove positivity

### For Analysis:
- `continuity` - prove continuity
- `differentiable` - prove differentiability  
- `simp [deriv_*]` - simplify derivatives
- `apply?` / `exact?` - search for lemmas

### For Existence Proofs:
- `use` - provide witness
- `refine ⟨_, _⟩` - construct exists proof
- `constructor` - split conjunctions

### For Inequalities:
- `linarith` - linear arithmetic
- `nlinarith` - nonlinear arithmetic (limited)
- `polyrith` - polynomial inequalities
- `gcongr` - monotonicity reasoning

### For Working with ODEs:
- Search Mathlib: `#check ODE` then tab-complete
- Look at `Mathlib.Analysis.ODE.*` modules
- Check examples in Mathlib docs

---

## Incremental Approach

**Start here** (easiest → hardest):

1. ✅ **Equilibrium existence** - Pure algebra, should be straightforward
2. ⚠️ **Boundedness** - Moderate difficulty, requires analysis
3. ⚠️ **Existence/uniqueness** - Depends on what's in Mathlib's ODE library
4. ❌ **Limit cycles** - Very hard, likely need axioms
5. ❌ **Kuramoto** - Very hard, start with simplified version

---

## Output Format

For each theorem you prove, provide:

```lean
-- Theorem [Name]
-- Strategy: [Your approach]
-- Dependencies: [Mathlib lemmas used]

[Any helper lemmas you define]

theorem [name] ... := by
  [Your complete proof]
  
-- Verification: [Explain why proof works]
```

---

## Additional Guidance

- **Don't be afraid of `sorry`**: If stuck, leave parts as `sorry` and document what's needed
- **Ask for help**: The Lean Zulip community is very helpful
- **Check Mathlib first**: Many lemmas you need might already exist
- **Prove lemmas separately**: Break complex proofs into manageable pieces
- **Use `#check` and `#print`**: Inspect existing definitions and theorems
- **Read Mathlib source**: See how similar proofs are done

## Success Criteria

A proof is complete when:
1. ✅ `lake build` succeeds with no errors
2. ✅ No `sorry` remains in the proof
3. ✅ All tactics succeed (no goals remaining)
4. ✅ Proof is readable and well-commented

---

## Example: Starter Proof for Equilibrium

Here's how you might begin:

```lean
theorem equilibrium_exists (params : Parameters) :
    ∃ s : State, IsEquilibrium params s ∧ s ∈ StateSpace := by
  -- Define equilibrium values
  let H_star := params.k1 / (params.k3 + params.k2 * params.k4 / params.k5)
  let P_star := (params.k4 / params.k5) * H_star
  
  -- Claim this is our equilibrium
  use ⟨H_star, P_star⟩
  
  constructor
  · -- Prove IsEquilibrium
    unfold IsEquilibrium vectorField
    simp [H_star, P_star]
    constructor
    · -- dH/dt = 0
      field_simp
      ring
    · -- dP/dt = 0  
      field_simp
      ring
      
  · -- Prove in StateSpace (both coordinates ≥ 0)
    unfold StateSpace
    constructor
    · -- H_star ≥ 0
      apply div_nonneg
      · exact params.k1_pos.le
      · apply add_pos
        · exact params.k3_pos
        · apply div_pos
          · exact mul_pos params.k2_pos params.k4_pos
          · exact params.k5_pos
    · -- P_star ≥ 0
      apply mul_nonneg
      · apply div_nonneg
        · exact params.k4_pos.le
        · exact params.k5_pos.le
      · -- H_star ≥ 0 (duplicate previous proof or make lemma)
        sorry
```

Now complete this and tackle the others! Good luck! 🎯