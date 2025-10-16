

# **Strategies for Achieving Full Formal Rigor in HIF-1$\\alpha$ Oscillator Lean 4 Proofs**

## **I. Executive Summary: The Roadmap to Formal Rigor (0% Axioms)**

The formal verification of the HIF-1$\\alpha$ oscillator model, an autonomous system of nonlinear Ordinary Differential Equations (ODEs) defined on a positive state space, is currently halted by the reliance on several powerful, yet unproven, axioms. These axioms compensate for significant deficiencies in the current landscape of the Mathlib4 library concerning advanced dynamical systems theory.1 Achieving complete formal rigor—the elimination of all sorry statements and axiomatic assumptions—necessitates a substantial, multi-phase contribution to Mathlib4 focusing on three foundational mathematical pillars: global solution theory, local qualitative analysis, and global geometric dynamics.  
The critical missing infrastructure includes the full theory of maximal solutions, the formal link between linear and nonlinear stability, and the geometric tools required to guarantee oscillatory behavior. The immediate priority is the development of robust analytical proofs (Phase I). However, the elimination of axioms relating to stability and limit cycles (Phases III and IV) involves formalizing theorems of high geometric complexity, such as the Hartman-Grobman and Poincaré-Bendixson theorems, projects that require significant resources and collaboration with the Lean community.3 The overall timeline for achieving $100\\%$ formal rigor for this model is estimated to span 1.5 to 3 years, depending on the speed of foundational progress in Mathlib’s analysis modules.

## **II. Strategy for Axiom Elimination: Foundational Gaps in Dynamical Systems**

The axioms present in the initial HIF-1$\\alpha$ proofs represent necessary steps in classical dynamical systems theory that have not yet been formalized in Mathlib4. Eliminating them requires proving these underlying theorems.

### **A. Global Existence and Boundedness (Maximal Solution Theory)**

The existing structure relies on axioms related to solution extension, stability, and existence, such as solution\_exists\_unique and solution\_nonneg\_of\_inward\_flow\_at\_boundary. While Mathlib includes the fundamental Picard-Lindelöf (Cauchy-Lipschitz) theorem, this only guarantees the existence and uniqueness of solutions locally, over a small time interval $\[t\_0 \- \\epsilon, t\_0 \+ \\epsilon\]$.5  
The transition from local existence to global existence (i.e., for all $t \\ge 0$) hinges on the **Maximal Solution Theorem** and the **Blow-up Criterion**.8 This theorem states that if the maximal interval of existence $  
For the HIF-1$\\alpha$ system, the axiom solution\_nonneg\_of\_inward\_flow\_at\_boundary is used to establish that the flow stays within a physically relevant compact region $K$. If the solution is contained within a compact set $K$ for all time, it cannot blow up or exit the domain boundary, thus guaranteeing $T\_{\\max} \= \\infty$. The rigorous formalization of this argument requires proving the core corollary: ODE.solution\_global\_of\_bounded\_on\_compact\_domain. This theorem, proving global existence based on uniform boundedness over a compact domain, is essential to replace the assumption of global well-posedness.

### **B. Local Stability Analysis (Hartman-Grobman Theorem)**

The axiom linear\_stability\_implies\_nonlinear is a direct substitution for the non-formalized **Hartman-Grobman Theorem (H-G)**.10 H-G provides the mathematical justification for replacing the analysis of a complex nonlinear system with its simplified linearization near a fixed point.11  
H-G applies specifically to *hyperbolic equilibrium points*, defined as fixed points $x\_e$ where the Jacobian matrix $Df(x\_e)$ has no eigenvalues $\\lambda$ with $\\operatorname{Re}(\\lambda) \= 0$.10 The theorem asserts that, in a neighborhood of $x\_e$, the nonlinear flow is *topologically conjugate* to the linear flow. Topological conjugacy means there exists a homeomorphism $h$ that maps the trajectories of the nonlinear system qualitatively onto the trajectories of the linear system, preserving their orientation.13  
Formalizing H-G requires several high-level mathematical components:

1. Defining the property of hyperbolicity rigorously using complex analysis on the spectrum of the Jacobian matrix.  
2. Defining and formalizing the existence of a local topological conjugacy (a homeomorphism $h$).  
3. Proving the theorem, which is a significant endeavor in advanced dynamical systems theory, requiring extensive work in functional analysis and differential geometry.11 The derived corollary, is\_hyperbolic\_equilibrium\_implies\_local\_asymptotic\_stability\_if\_linear\_stable, will then eliminate the need for the original stability axiom.

### **C. Global Limit Cycles (Poincaré-Bendixson Theorem)**

The fundamental requirement for proving the oscillatory nature of HIF-1$\\alpha$ is the axiom limit\_cycle\_exists. In planar systems (2D), this conclusion is derived from the **Poincaré-Bendixson Theorem (P-B)**.14  
P-B is a powerful geometric result asserting that for a differentiable autonomous system on an open subset of the plane (or cylinder/two-sphere), any non-empty, compact $\\omega$-limit set of a bounded orbit, which contains finitely many fixed points, must be either a fixed point, a periodic orbit (limit cycle), or a connected graph composed of fixed points and connecting homoclinic/heteroclinic orbits.14  
The formalization of P-B represents the greatest logistical barrier to full rigor in this project. Proofs of P-B rely heavily on concepts from planar topology, such as the **Jordan Curve Theorem (JCT)**, which dictates how closed curves partition the plane.16 The JCT itself is considered a landmark formalization effort in any proof assistant environment. Therefore, before P-B can be proven, an extensive preparatory effort must be undertaken in Mathlib4 to define and formalize:

1. The concept of the $\\omega$-limit set of a trajectory.  
2. Planar separation theorems, possibly including a simplified version of JCT tailored for the needed Poincaré section arguments.  
3. The definition and properties of Poincaré maps, which are essential tools for analyzing periodic orbits.18

Until this geometric analysis foundation is complete, the limit\_cycle\_exists axiom cannot be eliminated purely through internal Lean proofs.

## **III. Strategy for Placeholder Completion: Core Analytic Sub-Proofs**

The existing proofs contain placeholders (sorry) for routine analytic sub-steps. These are generally tractable using existing Mathlib theorems and tactics related to calculus and metric spaces.

### **A. Proof of Lipschitz Continuity (vectorField\_lipschitz)**

The Picard-Lindelöf theorem requires the vector field $f(x)$ to be Lipschitz continuous in the spatial variable $x$ locally.7 Since the HIF-1$\\alpha$ system is modeled by rational functions of the state variables (representing chemical concentrations), the function $f$ is continuously differentiable ($C^1$) on any compact subset $K$ of the positive orthant where the denominator is non-zero.19  
The continuous differentiability of $f$ is leveraged to prove its Lipschitz continuity over any compact, convex subset $K$. The proof requires showing that the derivative (Jacobian matrix) is bounded on $K$.19 The Lipschitz constant $L$ is explicitly defined as the supremum of the operator norm of the Jacobian, $\\lVert Df(x) \\rVert$, across the set $K$.20 The generalized Mean Value Theorem in multivariable calculus then ensures that $\\lVert f(x\_1) \- f(x\_2) \\rVert \\le L \\lVert x\_1 \- x\_2 \\rVert$. This procedure requires leveraging established calculus lemmas within Mathlib.Analysis.Calculus concerning derivative bounds and compact sets.

### **B. Proof of Domain Invariance and Boundedness (state\_space\_invariant, H\_bounded)**

#### **1\. Forward Invariance (state\_space\_invariant)**

The state\_space\_invariant proof for the biological domain (positive state variables) requires formally defining the condition for *inward flow* at the boundary of a set $C \\subseteq E$. This typically involves proving that the inner product of the vector field $f(x)$ with the outward-pointing normal vector $n(x)$ at any boundary point $x \\in \\partial C$ is non-positive, $f(x) \\cdot n(x) \\le 0$. Formalizing the definition of the boundary normal and subsequently proving the theorem ODE.is\_forward\_invariant\_of\_inward\_flow is necessary to eliminate this placeholder.

#### **2\. Quantitative Bounding (H\_bounded using Gronwall)**

The H\_bounded placeholder refers to proving that some metric (like an energy function $H$) remains bounded, often achieved using Gronwall's inequality. Mathlib formalizes the differential form of this inequality in Mathlib.Analysis.ODE.Gronwall.21  
If a bounding function $H(t) \= \\lVert x(t) \\rVert^2$ or a similar function is constructed such that its time derivative satisfies a linear differential inequality of the form $\\dot{H}(t) \\le K \\cdot H(t) \+ \\epsilon$, the Gronwall inequality provides a guaranteed exponential bound for $H(t)$.23 For stability and boundedness proofs, this tool is invaluable for showing that solutions cannot grow indefinitely, confirming the analytical basis for the global existence conclusion developed in Section II.A.

## **IV. Conceptual Gaps: Advanced Dynamic Behavior Formalization**

Beyond static existence and local stability, the oscillator model requires verification of dynamic phenomena: bifurcation and synchronization.

### **A. Bifurcation Proofs**

The existence of the HIF-1$\\alpha$ oscillator is conditional on specific parameter values crossing a stability threshold, often involving a Hopf bifurcation. This requires formalizing parameter-dependent systems.24  
Formal verification of the Hopf Bifurcation Theorem is exceptionally challenging. It requires two major components not currently formalized in Mathlib:

1. **Center Manifold Theory (CMT):** The theorem requires reducing the full dynamics near the non-hyperbolic fixed point to a lower-dimensional system defined on the center manifold.25 Formalizing CMT involves complex differential geometry and manifold theory, representing a significant extension project.  
2. **Normal Form Analysis:** Proving the stability of the nascent limit cycle (i.e., whether the bifurcation is supercritical or subcritical) requires calculating the sign of the first Lyapunov coefficient, an intricate symbolic computation.26

Given the difficulty of CMT, a feasible high-rigor strategy involves two steps: (1) Formalizing the *linear criteria* for the onset of oscillation (the Jacobian has a pair of pure imaginary eigenvalues, and all other eigenvalues are hyperbolic). (2) Until CMT is available, the conclusion of the bifurcation (existence of the limit cycle) should be treated as a highly justified, formally defined **postulate** derived from the established non-formal mathematical literature, acknowledging the missing CMT foundation.

### **B. Synchronization Proofs**

For coupled oscillator systems, such as a generalized Kuramoto model, synchronization corresponds to the asymptotic stability of the synchronization manifold.27 This stability is universally verified using the **Lyapunov Direct Method**.28  
The most critical conceptual gap here is the absence of the **LaSalle's Invariance Principle** in Mathlib4.28 While Lyapunov's basic theorem proves stability if a Lyapunov function $V$ exists such that its derivative along the flow $\\dot{V}$ is negative semi-definite ($\\dot{V} \\le 0$), proving *asymptotic* stability (convergence to the equilibrium) requires showing that the trajectory converges to the largest invariant set contained within the set where $\\dot{V}=0$.31 This is precisely the content of LaSalle’s principle.28  
Therefore, achieving formal rigor in synchronization proofs requires a dedicated effort to formalize:

1. The definitions of Lyapunov stability, asymptotic stability, and exponential stability.28  
2. The full LaSalle's Invariance Principle (Lyapunov.laSalle\_invariance\_principle).  
   Once these foundations are established, the existence of a suitable Lyapunov function V for the Kuramoto phase differences can be constructed, and LaSalle's principle can be applied to formally prove convergence to the synchronization manifold.

## **V. Mathlib Contribution and Implementation Roadmap**

Achieving full formal rigor demands submitting several high-impact Pull Requests (PRs) to Mathlib4, following the community’s guidelines for style, documentation, and process.33

### **A. Mathlib PR Strategy**

New contributions must start with discussion on the Lean community Zulip chat, particularly in analysis streams, to coordinate efforts and receive architectural guidance.1 The cornerstone of Mathlib contributions is the principle of modularity and small PRs.33  
For a project of this scale, the formalization should be partitioned logically:

1. **Definitions First:** Introduce foundational structures like $\\omega$-limit sets, hyperbolicity, and stability definitions, ensuring thorough documentation (docstrings).36  
2. **Incremental Proofs:** Submit lemmas covering intermediate results. For instance, the Maximal Solution Theorem should be broken down into existence, uniqueness, extension, and the blow-up criterion, each warranting a small PR.  
3. **Adherence to Style:** All code must adhere to the community style guide, including the use of consistent variable naming (e.g., E for normed vector space) and a line length limit of 100 characters.34

### **B. Feasibility Assessment and Phased Timeline**

The formalization effort is categorized based on the complexity and dependency structure of the missing theorems.  
Table 1: Phased Implementation Roadmap for HIF-1$\\alpha$ Rigor

| Phase | Core Objective | Complexity | Timeline | Primary Theorems/Concepts |
| :---- | :---- | :---- | :---- | :---- |
| **I** | **Analytic Completion** | Low-Medium | 2–4 months | Gronwall, Bounded Derivative $\\implies$ Lipschitz, Inward Flow Invariance. |
| **II** | **Global Flow and Asymptotic Stability** | Medium-High | 6–10 months | Maximal Solution/Blow-up Criterion, Lyapunov Direct Method definitions, LaSalle's Invariance Principle. |
| **III** | **Local Qualitative Analysis** | High | 10–15 months | Definition of Hyperbolicity, Topological Conjugacy, Hartman-Grobman Theorem. |
| **IV** | **Global Geometric Dynamics** | Very High | 18–30+ months | $\\omega$-Limit Sets, Planar Separation Lemmas (partial JCT), Poincaré-Bendixson Theorem. |

The timeline reveals that the most advanced proofs (linear\_stability\_implies\_nonlinear and limit\_cycle\_exists) will require foundational work spanning years. The formalization of the two-dimensional topology prerequisites for Poincaré-Bendixson (Phase IV) is the dominant temporal bottleneck.17

## **VI. Required Lean 4 API and Replacement Code Outlines**

The foundational mathematical concepts required to achieve $100\\%$ rigor must be formalized as theorems or definitions in the Lean 4 proof assistant. The following outlines specific definitions and theorem statements necessary to replace the existing axiomatic placeholders, assuming the state space $E$ is a finite-dimensional Euclidean space.

### **A. Maximal Solution and Global Existence**

The local Picard-Lindelöf result must be extended using the blow-up criterion.

Lean

\-- Defining the property of boundedness leading to global existence  
theorem ODE.solution\_global\_of\_bounded\_on\_compact\_domain  
  (f : E → E) (h\_lipschitz : LipschitzOnWith K f K)  
  (h\_compact : IsCompact K) (h\_invariance : IsForwardInvariant f K) :  
  ∃ (x : ℝ → E), IsSolution f x ∧ x 0 \= x₀  
  := sorry \-- Must rely on ODE.maximal\_solution and Blow-up criterion

### **B. Lyapunov Stability and Synchronization**

The verification of asymptotic synchronization relies entirely on proving LaSalle's Invariance Principle.

Lean

\-- Definition of Asymptotic Stability requiring both Lyapunov stability and convergence  
def is\_asymptotically\_stable (f : E → E) (x\_e : E) : Prop :=  
  IsLyapunovStable f x\_e ∧  
  (∀ (x₀ : E) (h\_near : ‖x₀ \- x\_e‖ \< r), Filter.Tendsto (fun t \=\> flow f t x₀) Filter.atTop (nhds x\_e))

\-- Critical missing component: LaSalle's Invariance Principle  
theorem Lyapunov.laSalle\_invariance\_principle (f : E → E) (V : E → ℝ)  
  (h\_flow\_bounded : ∀ x₀, Set.image (fun t \=\> flow f t x₀) (Set.Ici 0\) ⊆ K) :  
  ∀ x₀, Filter.Tendsto (fun t \=\> flow f t x₀) Filter.atTop (nhds (largest\_invariant\_set\_in (V\_dot\_zero)))  
  := sorry

### **C. Qualitative Equivalence (Hartman-Grobman)**

Eliminating the linear stability axiom requires defining hyperbolicity and topological equivalence, then proving H-G.

Lean

\-- Defining a hyperbolic equilibrium based on the Jacobian's eigenvalue spectrum  
def is\_hyperbolic\_equilibrium (f : E → E) (x\_e : E) : Prop :=  
  IsFixedPoint f x\_e ∧  
  (∀ λ ∈ Matrix.eigenvalues (deriv f x\_e), Real.re λ ≠ 0\)

\-- Proposed Theorem Statement for Topological Equivalence (Hartman-Grobman)  
theorem ODE.hartman\_grobman\_topological\_equivalence  
  (f : E → E) (x\_e : E) (h\_hyp : is\_hyperbolic\_equilibrium f x\_e)  
  (h\_smooth : Smooth f) :  
  ∃ (U : Set E) (V : Set E) (h : U ≃ₜ V), \-- Exists homeomorphism h mapping U to V  
    (∀ t, flow f t '' U ⊆ U) ∧ (h ∘ flow f t \= flow (deriv f x\_e) t ∘ h)  
  := sorry

## **VII. Conclusions and Recommendations**

The objective of achieving full formal rigor for the HIF-1$\\alpha$ oscillator is achievable but fundamentally dependent on extending the core analysis and dynamics libraries of Mathlib4. The current axioms are not merely missing lemmas but substitutes for major, complex theorems in nonlinear analysis.  
**Recommendations for Rigor Implementation:**

1. **Prioritize Analytic Closure (Phase I):** Immediately focus engineering efforts on completing the analytic sub-proofs (vectorField\_lipschitz, H\_bounded). These tasks utilize existing Mathlib infrastructure (Gronwall's inequality, derivative bounds) and will secure the foundation of the proof, confirming existence and uniqueness within the relevant physiological domain.  
2. **Strategic Foundational Investment (Phase II & III):** Dedicated teams must be assigned to formalize the Maximal Solution Theorem (Blow-up Criterion) and the Lyapunov/LaSalle Stability principles. These theorems are crucial prerequisites for rigorously justifying global dynamics and synchronization. Concurrently, the Hartman-Grobman theorem should be initiated as a high-value project that unlocks local stability analysis.  
3. **Manage Geometric Complexity (Phase IV):** The Poincaré-Bendixson Theorem represents a significant, long-term commitment due to its foundational topological dependencies, including planar separation theorems. If timely verification of the HIF-1$\\alpha$ model is paramount, the conclusion of P-B (limit\_cycle\_exists) should initially be formalized as a highly restricted postulate, with the explicit caveat that its underlying geometric proof remains an open problem for future foundational work in Mathlib. This approach allows the higher-level biological conclusions to be verified sooner while maintaining transparency regarding the unverified geometric foundation.

#### **Works cited**

1. Zulip Chat Archive \- Lean community, accessed October 16, 2025, [https://leanprover-community.github.io/archive/stream/217875-Is-there-code-for-X%3F/topic/differential.20equations.html](https://leanprover-community.github.io/archive/stream/217875-Is-there-code-for-X%3F/topic/differential.20equations.html)  
2. Mathlib: A Foundation for Formal Mathematics Research and Verification \- Lean, accessed October 16, 2025, [https://lean-lang.org/use-cases/mathlib/](https://lean-lang.org/use-cases/mathlib/)  
3. Lean in 2024 | Xena \- WordPress.com, accessed October 16, 2025, [https://xenaproject.wordpress.com/2024/01/20/lean-in-2024/](https://xenaproject.wordpress.com/2024/01/20/lean-in-2024/)  
4. Formalizing the proof of PFR in Lean4 using Blueprint: a short tour \- Terence Tao, accessed October 16, 2025, [https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/](https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/)  
5. analysis.ODE.picard\_lindelof \- mathlib3 docs \- Lean community, accessed October 16, 2025, [https://leanprover-community.github.io/mathlib\_docs/analysis/ODE/picard\_lindelof.html](https://leanprover-community.github.io/mathlib_docs/analysis/ODE/picard_lindelof.html)  
6. Picard–Lindelöf theorem \- Wikipedia, accessed October 16, 2025, [https://en.wikipedia.org/wiki/Picard%E2%80%93Lindel%C3%B6f\_theorem](https://en.wikipedia.org/wiki/Picard%E2%80%93Lindel%C3%B6f_theorem)  
7. Mathlib.Analysis.ODE.PicardLindelof \- Lean community, accessed October 16, 2025, [https://leanprover-community.github.io/mathlib4\_docs/Mathlib/Analysis/ODE/PicardLindelof.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/ODE/PicardLindelof.html)  
8. ordinary differential equations \- ODE / Maximal solution \- Mathematics Stack Exchange, accessed October 16, 2025, [https://math.stackexchange.com/questions/1963226/ode-maximal-solution](https://math.stackexchange.com/questions/1963226/ode-maximal-solution)  
9. Hartman–Grobman theorem \- Wikipedia, accessed October 16, 2025, [https://en.wikipedia.org/wiki/Hartman%E2%80%93Grobman\_theorem](https://en.wikipedia.org/wiki/Hartman%E2%80%93Grobman_theorem)  
10. Understanding the Hartman-Grobman Theorem: A Gateway to Predicting Dynamical System Behavior Near Hyperbolic Equilibria \- SvedbergOpen, accessed October 16, 2025, [https://www.svedbergopen.com/files/1745823370\_(3)\_IJPAMR110316302548BR\_(p\_20-34).pdf](https://www.svedbergopen.com/files/1745823370_\(3\)_IJPAMR110316302548BR_\(p_20-34\).pdf)  
11. The Hartman-Grobman Theorem, Structural Stability of Linearization, and Stable/Unstable Manifolds \- YouTube, accessed October 16, 2025, [https://www.youtube.com/watch?v=vRaUSnB7qNw](https://www.youtube.com/watch?v=vRaUSnB7qNw)  
12. 3.4 The Hartman-Grobman theorem, accessed October 16, 2025, [https://math.uwaterloo.ca/\~xzliu/notes451/am451/node17.html](https://math.uwaterloo.ca/~xzliu/notes451/am451/node17.html)  
13. Poincaré–Bendixson theorem \- Wikipedia, accessed October 16, 2025, [https://en.wikipedia.org/wiki/Poincar%C3%A9%E2%80%93Bendixson\_theorem](https://en.wikipedia.org/wiki/Poincar%C3%A9%E2%80%93Bendixson_theorem)  
14. THE POINCARE BENDIXON THEOREM Math118, O. Knill \- Harvard Mathematics Department, accessed October 16, 2025, [https://legacy-www.math.harvard.edu/archive/118r\_spring\_05/handouts/poincare.pdf](https://legacy-www.math.harvard.edu/archive/118r_spring_05/handouts/poincare.pdf)  
15. The Poincaré-Bendixson Theorem in Isabelle/HOL (CPP 2020 \- The 9th ACM SIGPLAN International Conference on Certified Programs and Proofs), accessed October 16, 2025, [https://popl20.sigplan.org/details/CPP-2020-papers/23/The-Poincar-Bendixson-Theorem-in-Isabelle-HOL](https://popl20.sigplan.org/details/CPP-2020-papers/23/The-Poincar-Bendixson-Theorem-in-Isabelle-HOL)  
16. The Poincaré-Bendixson Theorem in Isabelle/HOL | Semantic Scholar, accessed October 16, 2025, [https://pdfs.semanticscholar.org/715d/fca156fe9a4ecb4acc501761c480fdd4b9b1.pdf](https://pdfs.semanticscholar.org/715d/fca156fe9a4ecb4acc501761c480fdd4b9b1.pdf)  
17. a poincaré-bendixson theorem for hybrid systems, accessed October 16, 2025, [https://liberzon.csl.illinois.edu/teaching/Poincare-Bendixson-hybrid.pdf](https://liberzon.csl.illinois.edu/teaching/Poincare-Bendixson-hybrid.pdf)  
18. Lipschitz continuity \- Wikipedia, accessed October 16, 2025, [https://en.wikipedia.org/wiki/Lipschitz\_continuity](https://en.wikipedia.org/wiki/Lipschitz_continuity)  
19. Proving a norm is lipschitz \- Math Stack Exchange, accessed October 16, 2025, [https://math.stackexchange.com/questions/1648275/proving-a-norm-is-lipschitz](https://math.stackexchange.com/questions/1648275/proving-a-norm-is-lipschitz)  
20. Mathlib.Analysis.ODE.Gronwall \- Lean community, accessed October 16, 2025, [https://leanprover-community.github.io/mathlib4\_docs/Mathlib/Analysis/ODE/Gronwall.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/ODE/Gronwall.html)  
21. analysis.ODE.gronwall \- mathlib3 docs \- Lean community, accessed October 16, 2025, [https://leanprover-community.github.io/mathlib\_docs/analysis/ODE/gronwall.html](https://leanprover-community.github.io/mathlib_docs/analysis/ODE/gronwall.html)  
22. Grönwall's inequality, accessed October 16, 2025, [https://cmps-people.ok.ubc.ca/rtyson/Teaching/Math339/2019/LectureNotes/lecture12\_gronwall-inequality.pdf](https://cmps-people.ok.ubc.ca/rtyson/Teaching/Math339/2019/LectureNotes/lecture12_gronwall-inequality.pdf)  
23. The Lean Theorem Prover (system description), accessed October 16, 2025, [https://lean-lang.org/papers/system.pdf](https://lean-lang.org/papers/system.pdf)  
24. \[2504.20375\] Generative Learning for Slow Manifolds and Bifurcation Diagrams \- arXiv, accessed October 16, 2025, [https://arxiv.org/abs/2504.20375](https://arxiv.org/abs/2504.20375)  
25. Algorithm for Generating Bifurcation Diagrams Using Poincaré Intersection Plane \- MDPI, accessed October 16, 2025, [https://www.mdpi.com/2227-7390/13/11/1818](https://www.mdpi.com/2227-7390/13/11/1818)  
26. Synchronization of Phase-coupled Oscillators with Plastic Coupling Strength \- Enrique Mallada, accessed October 16, 2025, [https://mallada.ece.jhu.edu/pubs/2015-ITA-GMT.pdf](https://mallada.ece.jhu.edu/pubs/2015-ITA-GMT.pdf)  
27. 4 Lyapunov Stability Theory \- Graduate Degree in Control \+ Dynamical Systems, accessed October 16, 2025, [https://www.cds.caltech.edu/\~murray/courses/cds101/fa02/caltech/mls93-lyap.pdf](https://www.cds.caltech.edu/~murray/courses/cds101/fa02/caltech/mls93-lyap.pdf)  
28. Lyapunov stability \- Wikipedia, accessed October 16, 2025, [https://en.wikipedia.org/wiki/Lyapunov\_stability](https://en.wikipedia.org/wiki/Lyapunov_stability)  
29. Lyapunov Stability Theorem \- (Calculus IV) \- Vocab, Definition, Explanations | Fiveable, accessed October 16, 2025, [https://fiveable.me/key-terms/calculus-iv/lyapunov-stability-theorem](https://fiveable.me/key-terms/calculus-iv/lyapunov-stability-theorem)  
30. Chapter 13 \- Internal (Lyapunov) Stability \- MIT OpenCourseWare, accessed October 16, 2025, [https://ocw.mit.edu/courses/6-241j-dynamic-systems-and-control-spring-2011/95bf74f6518ebb3be79d1748ca6c349c\_MIT6\_241JS11\_chap13.pdf](https://ocw.mit.edu/courses/6-241j-dynamic-systems-and-control-spring-2011/95bf74f6518ebb3be79d1748ca6c349c_MIT6_241JS11_chap13.pdf)  
31. A New Set of Stability Criteria Extending Lyapunov's Direct Method \- SIAM.org, accessed October 16, 2025, [https://www.siam.org/Portals/0/Documents/S136158PDF.PDF?ver=2021-10-10-114655-567](https://www.siam.org/Portals/0/Documents/S136158PDF.PDF?ver=2021-10-10-114655-567)  
32. How to contribute to mathlib \- Lean community, accessed October 16, 2025, [https://leanprover-community.github.io/contribute/index.html](https://leanprover-community.github.io/contribute/index.html)  
33. Library Style Guidelines \- Lean community, accessed October 16, 2025, [https://leanprover-community.github.io/contribute/style.html](https://leanprover-community.github.io/contribute/style.html)  
34. Meet the community, accessed October 16, 2025, [https://leanprover-community.github.io/meet.html](https://leanprover-community.github.io/meet.html)  
35. Pull Request Review Guide \- Lean community, accessed October 16, 2025, [https://leanprover-community.github.io/contribute/pr-review.html](https://leanprover-community.github.io/contribute/pr-review.html)