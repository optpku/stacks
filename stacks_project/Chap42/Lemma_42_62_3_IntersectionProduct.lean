/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap42.Lemma_42_62_1_IntersectionProduct

/-!
# Total intersection products of Chow classes over a field

This file assembles the homogeneous section 42.62 product `α · β = Δ!(α × β)`
into a bilinear operation on total Chow homology of a scheme locally of finite
type over a field.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules hiding dual

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

variable {k : Type u} [Field k]

namespace Total

/-- The intersection product of total Chow classes on a scheme over a field, obtained by
capping the total exterior product with the canonical Gysin class of the diagonal. -/
noncomputable def intersectionProduct (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecialization X r) :
    Total (fun _ ↦ 0) X →+ Total (fun _ ↦ 0) X →+ Total (fun _ ↦ 0) X :=
  (BivariantClass.totalCap (fun _ ↦ 0) (diagonalGysinClass X r D)
      (𝟙 X) (diagonal X) (𝟙 (X ⨯ X)) IsPullback.of_id_fst).compHom.comp
    (exteriorProduct X X)

/-- The total intersection product is the total cap of the exterior product by the
canonical diagonal Gysin class. -/
theorem intersectionProduct_def (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecialization X r)
    (alpha beta : Total (fun _ ↦ 0) X) :
    intersectionProduct X r D alpha beta =
      BivariantClass.totalCap (fun _ ↦ 0) (diagonalGysinClass X r D)
        (𝟙 X) (diagonal X) (𝟙 (X ⨯ X)) IsPullback.of_id_fst
        (exteriorProduct X X alpha beta) := sorry

/-- The total intersection product of homogeneous classes is the homogeneous degreewise
product in degree `n + m - r`. -/
theorem intersectionProduct_of (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] {n m : ℤ} (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecialization X r)
    (alpha : RelativeChow (fun _ ↦ 0) X n)
    (beta : RelativeChow (fun _ ↦ 0) X m) :
    intersectionProduct X r D (DirectSum.of _ n alpha) (DirectSum.of _ m beta) =
      DirectSum.of (fun d : ℤ ↦ RelativeChow (fun _ ↦ 0) X d) (n + m - r)
        (ChowGroup.intersectionProduct X r D alpha beta) := sorry

end Total

end AlgebraicGeometry.ChowGroup
