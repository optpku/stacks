module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Proper.Reduced.Valuation
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 38.19.7: a proper flat scheme over the spectrum of a valuation ring is reduced if
its special fibre is reduced. -/
@[stacks 0H2T] #check
  (AlgebraicGeometry.Scheme.Hom.isReduced_of_proper_flat_of_isReduced_specialFiber :
    ∀ {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] [Flat f]
      [IsReduced (f.fiber (IsLocalRing.closedPoint R))],
      IsReduced X)

/- Companion to Lemma 38.19.7: under the same assumptions, every fibre over the valuation
ring is reduced. -/
#check
  (AlgebraicGeometry.Scheme.Hom.isReduced_fiber_of_proper_flat_of_isReduced_specialFiber :
    ∀ {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] [Flat f]
      [IsReduced (f.fiber (IsLocalRing.closedPoint R))]
      (s : Spec (CommRingCat.of R)),
      IsReduced (f.fiber s))

end AlgebraicGeometry.Scheme.Hom
