/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.ThickeningExtension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder

/-!
# Étale preservation and descent of universal first-order thickenings

Universality is preserved by cartesian étale lifts and descends along
surjective étale morphisms of first-order thickenings.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsUniversalFirstOrder

/-- A cartesian étale lift of a universal first-order thickening remains a
universal first-order thickening. -/
theorem of_etale {S : Scheme.{u}} {X Y Z Y' Z' : AlgebraicSpace S}
    (fZY : Z ⟶ Y) (iY : Y ⟶ Y') (fY' : Y' ⟶ X) (iZ : Z ⟶ Z') (fZ' : Z' ⟶ Y')
    [Etale fZY] [IsUniversalFirstOrder iY fY'] [Etale fZ']
    (h : IsPullback iZ fZY fZ' iY) :
    IsUniversalFirstOrder iZ (fZ' ≫ fY') :=
  sorry

/-- Universality of a first-order thickening descends along a surjective étale
cartesian morphism of first-order thickenings. -/
theorem of_etale_surjective {S : Scheme.{u}} {X Y Z Y' Z' : AlgebraicSpace S}
    (fZY : Z ⟶ Y) (iY : Y ⟶ Y') (fY' : Y' ⟶ X) (iZ : Z ⟶ Z') (fZ' : Z' ⟶ Y')
    [Etale fZY] [Surjective fZY] [IsFirstOrderThickening iY] [Etale fZ']
    [IsUniversalFirstOrder iZ (fZ' ≫ fY')]
    (h : IsPullback iZ fZY fZ' iY) :
    IsUniversalFirstOrder iY fY' :=
  sorry

/-- The canonical étale inverse image of a universal first-order thickening is
again a universal first-order thickening. -/
instance etaleExtend_isUniversal {S : Scheme.{u}} {X Y Z Y' : AlgebraicSpace S}
    (fZY : Z ⟶ Y) (iY : Y ⟶ Y') (fY' : Y' ⟶ X)
    [Etale fZY] [IsUniversalFirstOrder iY fY'] :
    IsUniversalFirstOrder (etaleExtendImmersion fZY iY)
      (etaleExtendHom fZY iY ≫ fY') :=
  sorry

end IsUniversalFirstOrder

end AlgebraicGeometry.AlgebraicSpace
