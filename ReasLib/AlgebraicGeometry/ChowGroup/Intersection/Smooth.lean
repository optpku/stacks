/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.OpenImmersion
public import ReasLib.AlgebraicGeometry.BivariantClass.Smooth
public import ReasLib.AlgebraicGeometry.ChowGroup.Intersection.Over

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules hiding dual

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

variable {k : Type u} [Field k]

/-- The diagonal class of a smooth constant-dimensional scheme is the inverse image of
identity flat pullback under smooth composition with the first product projection. -/
def diagonalGysinClassSmooth (X : SchemeOverField k) [Smooth X.hom] (d : ℕ)
    [RelativeDimension X.hom d] :
    BivariantClass.group (fun _ ↦ 0) (diagonal X) (d : ℤ) :=
  (BivariantClass.compSmoothEquiv (fun _ ↦ 0) (diagonal X)
    (prod.fst : X ⨯ X ⟶ X) d (d : ℤ)).symm
      (Eq.mpr (congrArg (fun f : X ⟶ X ↦ BivariantClass (fun _ ↦ 0) f
          ((d : ℤ) - d)) (prod.lift_fst (𝟙 X) (𝟙 X)))
        (Eq.mpr (congrArg (fun p : ℤ ↦ BivariantClass (fun _ ↦ 0) (𝟙 X) p)
          (sub_self (d : ℤ)))
          (BivariantClass.flatPullback (fun _ ↦ 0) (𝟙 X) 0)))

/-- Smooth composition of the diagonal class with the first projection is identity flat
pullback, with its morphism and degree transported to the composite. -/
theorem diagonalGysinClassSmooth_comp (X : SchemeOverField k) [Smooth X.hom] (d : ℕ)
    [RelativeDimension X.hom d] :
    BivariantClass.compSmoothEquiv (fun _ ↦ 0) (diagonal X)
        (prod.fst : X ⨯ X ⟶ X) d (d : ℤ) (diagonalGysinClassSmooth X d) =
      (Eq.mpr (congrArg (fun f : X ⟶ X ↦ BivariantClass (fun _ ↦ 0) f
          ((d : ℤ) - d)) (prod.lift_fst (𝟙 X) (𝟙 X)))
        (Eq.mpr (congrArg (fun p : ℤ ↦ BivariantClass (fun _ ↦ 0) (𝟙 X) p)
          (sub_self (d : ℤ)))
          (BivariantClass.flatPullback (fun _ ↦ 0) (𝟙 X) 0))) := sorry

/-- The intersection product on a smooth constant-dimensional scheme is diagonal cap of
the exterior product. -/
def smoothIntersectionProduct (X : SchemeOverField k) [Smooth X.hom] (d : ℕ)
    [RelativeDimension X.hom d] {n m : ℤ}
    (alpha : RelativeChow (fun _ ↦ 0) X n)
    (beta : RelativeChow (fun _ ↦ 0) X m) :
    RelativeChow (fun _ ↦ 0) X (n + m - d) :=
  (diagonalGysinClassSmooth X d).cap (𝟙 X) (diagonal X) (𝟙 (X ⨯ X))
    IsPullback.of_id_fst (n + m) (exteriorProductPairing X X n m alpha beta)

/-- Intersection over a smooth constant-dimensional scheme is diagonal cap of the exterior
product on the cartesian comparison square. -/
def smoothIntersectionProductOver (X : SchemeOverField k) [Smooth X.hom]
    {Y Z : SchemeOverField k} (fY : Y ⟶ X) (fZ : Z ⟶ X)
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    [LocallyOfFiniteType fY.left] [LocallyOfFiniteType fZ.left]
    (d : ℕ) [RelativeDimension X.hom d] {n m : ℤ}
    (alpha : RelativeChow (fun _ ↦ 0) Y n)
    (beta : RelativeChow (fun _ ↦ 0) Z m) :
    RelativeChow (fun _ ↦ 0) (pullback fY fZ) (n + m - d) :=
  (diagonalGysinClassSmooth X d).cap (Dedekind.fiberProductToBase fY fZ)
    (Dedekind.fiberProductToProduct fY fZ) (prod.map fY fZ)
    (Dedekind.intersectionSquare_isPullback fY fZ) (n + m)
    (exteriorProductPairing Y Z n m alpha beta)

/-- The smooth diagonal product agrees with the product from every explicit diagonal
deformation presentation. -/
theorem smoothIntersectionProduct_eq (X : SchemeOverField k) [Smooth X.hom] (d : ℕ)
    [RelativeDimension X.hom d]
    [IsFiniteLocallyFreeOfRank d (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecialization X d) {n m : ℤ}
    (alpha : RelativeChow (fun _ ↦ 0) X n)
    (beta : RelativeChow (fun _ ↦ 0) X m) :
    smoothIntersectionProduct X d alpha beta = intersectionProduct X d D alpha beta := sorry

/-- The smooth diagonal product over a scheme agrees with the product from every explicit
diagonal deformation presentation. -/
theorem smoothIntersectionProductOver_eq (X : SchemeOverField k) [Smooth X.hom]
    {Y Z : SchemeOverField k} (fY : Y ⟶ X) (fZ : Z ⟶ X)
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    [LocallyOfFiniteType fY.left] [LocallyOfFiniteType fZ.left]
    (d : ℕ) [RelativeDimension X.hom d]
    [IsFiniteLocallyFreeOfRank d (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecialization X d) {n m : ℤ}
    (alpha : RelativeChow (fun _ ↦ 0) Y n)
    (beta : RelativeChow (fun _ ↦ 0) Z m) :
    smoothIntersectionProductOver X fY fZ d alpha beta =
      intersectionProductOver X fY fZ d D alpha beta := sorry

end AlgebraicGeometry.ChowGroup
