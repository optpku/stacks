/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.GenericFiber.Connected
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.28.7: let `f : X ⟶ Spec (CommRingCat.of R)` be flat, where `R` is a
discrete valuation ring. If `X` is connected and the closed fibre is reduced, then the
generic fibre is connected. -/
@[stacks 055J] #check
  (AlgebraicGeometry.Scheme.Hom.connectedSpace_genericFiber_of_isReduced_specialFiber :
    ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] [ConnectedSpace X]
      [IsReduced (f.fiber (IsLocalRing.closedPoint R))],
      ConnectedSpace (f.fiber (genericPoint (Spec (CommRingCat.of R)))))

end AlgebraicGeometry.Scheme.Hom
