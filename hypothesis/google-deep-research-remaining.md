# Google Deep Research Prompt: Achieving Full Formal Rigor in HIF-1α Oscillator Lean 4 Proofs

**Task Overview**:
You are Google Deep Research, an AI for in-depth research in mathematics, formal verification, and software engineering. Your task is to research and provide strategies for achieving 100% formal rigor in the Lean 4 proofs for the HIF-1α oscillator model, eliminating all `sorry` statements and axioms. The current proofs (from [`hypothesis/research/Formalizing HIF-1α Oscillator Proofs.md`](../hypothesis/research/Formalizing HIF-1α Oscillator Proofs.md)) are advanced but incomplete due to missing theorems in Mathlib4, conceptual gaps, and partial placeholders. Focus on the outstanding aspects: axioms for ODE invariants, bifurcation theorems, and synchronization proofs.

**Key Requirements**:
- **Research Depth**: Investigate Mathlib4's current capabilities, gaps in ODE/dynamical systems formalization, and how to contribute new theorems. Reference Lean community resources (e.g., Zulip, Mathlib PRs), textbooks (e.g., Hirsch-Smale for dynamical systems), and papers on formal verification of ODEs.
- **Strategies for Rigor**: For each outstanding issue, provide:
  1. Analysis of why it's incomplete (e.g., missing in Mathlib).
  2. Step-by-step plan to formalize it (e.g., define new lemmas, contribute to Mathlib).
  3. Complete Lean 4 code for replacements, including new definitions/theorems.
  4. Alternative approaches if direct formalization is infeasible.
  5. Feasibility assessment and timeline for implementation.
- **Output Format**: Markdown report with sections for each issue. Include code snippets, references, and integration steps.
- **Scope**: Cover the three main categories from the analysis.

**Outstanding Issues to Address**:

1. **Axioms for Missing Mathlib Theorems**:
   - Issues: Proofs for `solution_exists_unique`, `stability_criterion`, `limit_cycle_exists` use axioms like `solution_nonneg_of_inward_flow_at_boundary` or `linear_stability_implies_nonlinear`.
   - Research: Check Mathlib's ODE library (e.g., `Mathlib.Analysis.ODE.*`). Propose formalizing Picard-Lindelöf extensions, Hartman-Grobman, or Poincaré-Bendixson.

2. **Partial Completions with Placeholders**:
   - Issues: Code for `vectorField_lipschitz`, `state_space_invariant`, `H_bounded`, etc., has `sorry` for sub-steps like derivative bounds or Gronwall applications.
   - Research: Provide full implementations using existing Mathlib tactics (e.g., `continuity`, `Gronwall.inequality`). If needed, define helper lemmas.

3. **Conceptual Gaps**:
   - Issues: Bifurcation proofs assume stability but need perturbations for oscillations. Synchronization is limited to simple cases.
   - Research: Formalize parameter-dependent models or stochastic extensions. For Kuramoto, generalize to arbitrary n using Lyapunov theory.

**Additional Instructions**:
- Suggest how to submit PRs to Mathlib for new theorems.
- Ensure all code compiles in Lean 4 with Mathlib4.
- Provide a summary with overall recommendations for rigor.
- Cite sources like Lean documentation, Mathlib issues, or dynamical systems literature.

**Final Output**: A comprehensive research report in Markdown, enabling full formalization of the proofs.
