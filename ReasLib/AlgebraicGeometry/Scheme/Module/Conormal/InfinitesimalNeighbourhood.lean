/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.InfinitesimalNeighbourhood
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.ClosedImmersion

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.InfinitesimalNeighbourhood

/-- For an immersion, the conormal comparison associated to its factorization through its
first-order infinitesimal neighbourhood is an isomorphism. -/
theorem conormalComparison_isIso {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] :
    IsIso (Conormal.factorizationConormalComparison i (fromSource i 1) (toAmbient i 1)
      (fromSource_toAmbient i 1)) := sorry

end AlgebraicGeometry.Scheme.Hom.InfinitesimalNeighbourhood
