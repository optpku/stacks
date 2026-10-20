/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Proper.Reduced

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.26.6 (1): a proper scheme over a discrete valuation ring is reduced if every
irreducible component dominates the base and the special fiber is reduced. -/
@[stacks 0C0D] #check
  (AlgebraicGeometry.Scheme.Hom.isReduced_of_isReduced_specialFiber :
    ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
      (hdominant : ∀ Z : irreducibleComponents X,
        IsDominant (X.irreducibleComponentSubschemeι Z ≫ f))
      [IsReduced (f.fiber (IsLocalRing.closedPoint R))],
      IsReduced X)

/- Companion clause: under the same hypotheses, the generic fiber is reduced. -/
#check
  (AlgebraicGeometry.Scheme.Hom.isReduced_genericFiber_of_isReduced_specialFiber :
    ∀ {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
      (hdominant : ∀ Z : irreducibleComponents X,
        IsDominant (X.irreducibleComponentSubschemeι Z ≫ f))
      [IsReduced (f.fiber (IsLocalRing.closedPoint R))],
      IsReduced (f.fiber (genericPoint (Spec (CommRingCat.of R)))))

end AlgebraicGeometry.Scheme.Hom
