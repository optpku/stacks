/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Ph.Adjunction
import StacksCheckRecall

/-!
# Lemma 84.8.2

For `K` in `D⁺(X_étale)` on an algebraic space `X` over a scheme `S`, with torsion
cohomology sheaves, the canonical maps `π_X⁻¹ K ⟶ Rε_{X,*}(a_X⁻¹ K)` and
`K ⟶ Ra_{X,*}(a_X⁻¹ K)` are isomorphisms, where `a_X = π_X ∘ ε_X` is the morphism
of topoi `Sh((Spaces/X)_ph) ⟶ Sh(X_étale)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.PhComparison
open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology

universe u

/- Lemma 84.8.2: the canonical ph comparison and derived adjunction units are isomorphisms
on bounded-below objects with torsion cohomology. -/
@[stacks 0DGU] #check (AlgebraicGeometry.AlgebraicSpace.PhComparison.piInverseDerivedUnit_isIso :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn
      (Sheaf.torsion (smallEtaleTopology X)) K),
    IsIso (piInverseDerivedUnit X K))

#check (AlgebraicGeometry.AlgebraicSpace.PhComparison.plusAAdjunction_unit_isIso :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn
      (Sheaf.torsion (smallEtaleTopology X)) K),
    IsIso ((plusAAdjunction X).unit.app K))

end
