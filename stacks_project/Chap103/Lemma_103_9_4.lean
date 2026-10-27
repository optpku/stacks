/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Quasicoherent.ParasiticHomology
import StacksCheckRecall

/-! # Exactness of quasi-coherent complexes versus parasitic homology -/

open AlgebraicGeometry CategoryTheory GroupoidsOver

universe u

/- Lemma 103.9.4: a composite-zero pair of quasi-coherent module maps on an
algebraic stack is exact in the abelian category of quasi-coherent modules if
and only if its homology computed in étale or fppf modules is parasitic. -/
@[stacks 0776] #check
  (AlgebraicGeometry.GroupoidsOver.QCoh.exact_iff_homology_isParasitic :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
      (sc : ShortComplex (QCoh X)) {τ : StandardTopology},
      (τ = .etale ∨ τ = .fppf) →
        (sc.Exact ↔ IsParasitic
          (associatedModulePresheaf (QCoh.associatedHomology X τ sc))))
