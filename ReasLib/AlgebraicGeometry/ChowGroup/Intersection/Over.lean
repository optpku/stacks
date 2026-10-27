/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Intersection.Diagonal
public import ReasLib.AlgebraicGeometry.ChowGroup.Dedekind.ExteriorProduct.Cap
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Over
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Product
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc

/-!
# Fiber-product comparison geometry and intersection products

The diagonal comparison square over an arbitrary scheme identifies a fiber product over
a scheme with the pullback of its diagonal. These comparison morphisms and the finite-type
instances support intersection products over general bases.

Exterior products followed by diagonal Gysin action give bilinear intersection products.
The clopen rank loci of the diagonal allow arbitrary smooth bases, including bases whose
connected components have different dimensions.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules hiding dual

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.Dedekind

/-- The diagonal morphism of a scheme over a base, as a morphism in `Over S`. -/
noncomputable abbrev diagonal {S : Scheme.{u}} (X : Over S) : X ⟶ X ⨯ X :=
  prod.lift (𝟙 X) (𝟙 X)

/-- The fiber product of two schemes locally of finite type over `S` remains locally of
finite type over `S`. -/
instance pullback_locallyOfFiniteType {S : Scheme.{u}} {X Y Z : Over S}
    (fY : Y ⟶ X) (fZ : Z ⟶ X)
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom] :
    LocallyOfFiniteType (pullback fY fZ).hom := sorry

/-- The product of two locally finite-type morphisms over `S` is locally of finite type. -/
instance prodMap_locallyOfFiniteType {S : Scheme.{u}} {X Y Z : Over S}
    (fY : Y ⟶ X) (fZ : Z ⟶ X)
    [LocallyOfFiniteType fY.left] [LocallyOfFiniteType fZ.left] :
    LocallyOfFiniteType (prod.map fY fZ).left := sorry

/-- The structure morphism of a fiber product over `X` to the base object `X`. -/
noncomputable abbrev fiberProductToBase {S : Scheme.{u}} {X Y Z : Over S}
    (fY : Y ⟶ X) (fZ : Z ⟶ X) :
    pullback fY fZ ⟶ X :=
  pullback.fst fY fZ ≫ fY

/-- The comparison from a fiber product over `X` to the product over `S`. -/
noncomputable abbrev fiberProductToProduct {S : Scheme.{u}} {X Y Z : Over S}
    (fY : Y ⟶ X) (fZ : Z ⟶ X) :
    pullback fY fZ ⟶ Y ⨯ Z :=
  prod.lift (pullback.fst fY fZ) (pullback.snd fY fZ)

/-- The comparison square identifying `Y ×_X Z` with the pullback of the diagonal
along `Y ×_S Z ⟶ X ×_S X`. -/
theorem intersectionSquare_isPullback {S : Scheme.{u}} {X Y Z : Over S}
    (fY : Y ⟶ X) (fZ : Z ⟶ X) :
    IsPullback (fiberProductToBase fY fZ).left (fiberProductToProduct fY fZ).left
      (diagonal X).left (prod.map fY fZ).left := sorry

end AlgebraicGeometry.ChowGroup.Dedekind

namespace AlgebraicGeometry.ChowGroup

variable {k : Type u} [Field k]

/-- The intersection product of homogeneous Chow classes of schemes locally of finite type
over `X`, obtained by capping the exterior product with the canonical Gysin class of the
diagonal. -/
noncomputable def intersectionProductOver (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] {Y Z : SchemeOverField k} (fY : Y ⟶ X) (fZ : Z ⟶ X)
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    [LocallyOfFiniteType fY.left] [LocallyOfFiniteType fZ.left]
    {n m : ℤ} (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecialization X r)
    (alpha : RelativeChow (fun _ ↦ 0) Y n)
    (beta : RelativeChow (fun _ ↦ 0) Z m) :
    RelativeChow (fun _ ↦ 0) (pullback fY fZ) (n + m - r) :=
  (diagonalGysinClass X r D).cap (Dedekind.fiberProductToBase fY fZ)
    (Dedekind.fiberProductToProduct fY fZ) (prod.map fY fZ)
    (Dedekind.intersectionSquare_isPullback fY fZ) (n + m)
    (exteriorProductPairing Y Z n m alpha beta)

/-- The over-`X` intersection product is the comparison-square cap of the Chow exterior
product by the canonical diagonal Gysin class. -/
theorem intersectionProductOver_def (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] {Y Z : SchemeOverField k} (fY : Y ⟶ X) (fZ : Z ⟶ X)
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    [LocallyOfFiniteType fY.left] [LocallyOfFiniteType fZ.left]
    {n m : ℤ} (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecialization X r)
    (alpha : RelativeChow (fun _ ↦ 0) Y n)
    (beta : RelativeChow (fun _ ↦ 0) Z m) :
    intersectionProductOver X fY fZ r D alpha beta =
      (diagonalGysinClass X r D).cap (Dedekind.fiberProductToBase fY fZ)
        (Dedekind.fiberProductToProduct fY fZ) (prod.map fY fZ)
        (Dedekind.intersectionSquare_isPullback fY fZ) (n + m)
        (exteriorProductPairing Y Z n m alpha beta) := rfl

namespace Total

/-- The intersection product of total Chow classes of schemes locally of finite type over
`X`, obtained by capping the total exterior product with the canonical Gysin class of the
diagonal. -/
noncomputable def intersectionProductOver (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] {Y Z : SchemeOverField k} (fY : Y ⟶ X) (fZ : Z ⟶ X)
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    [LocallyOfFiniteType fY.left] [LocallyOfFiniteType fZ.left] (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecialization X r) :
    Total (fun _ ↦ 0) Y →+ Total (fun _ ↦ 0) Z →+ Total (fun _ ↦ 0) (pullback fY fZ) :=
  (Dedekind.Total.cap (fun _ ↦ 0) (diagonalGysinClass X r D)
      (Dedekind.fiberProductToBase fY fZ) (Dedekind.fiberProductToProduct fY fZ)
      (prod.map fY fZ) (Dedekind.intersectionSquare_isPullback fY fZ)).compHom.comp
    (exteriorProduct Y Z)

/-- The total over-`X` intersection product is the total cap of the exterior product by the
canonical diagonal Gysin class. -/
theorem intersectionProductOver_def (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] {Y Z : SchemeOverField k} (fY : Y ⟶ X) (fZ : Z ⟶ X)
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    [LocallyOfFiniteType fY.left] [LocallyOfFiniteType fZ.left] (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecialization X r)
    (alpha : Total (fun _ ↦ 0) Y) (beta : Total (fun _ ↦ 0) Z) :
    intersectionProductOver X fY fZ r D alpha beta =
      Dedekind.Total.cap (fun _ ↦ 0) (diagonalGysinClass X r D)
        (Dedekind.fiberProductToBase fY fZ) (Dedekind.fiberProductToProduct fY fZ)
        (prod.map fY fZ) (Dedekind.intersectionSquare_isPullback fY fZ)
        (exteriorProduct Y Z alpha beta) := rfl

/-- The total over-`X` intersection product of homogeneous classes is the homogeneous
degreewise product in degree `n + m - r`. -/
theorem intersectionProductOver_of (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] {Y Z : SchemeOverField k} (fY : Y ⟶ X) (fZ : Z ⟶ X)
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    [LocallyOfFiniteType fY.left] [LocallyOfFiniteType fZ.left]
    {n m : ℤ} (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecialization X r)
    (alpha : RelativeChow (fun _ ↦ 0) Y n)
    (beta : RelativeChow (fun _ ↦ 0) Z m) :
    intersectionProductOver X fY fZ r D (DirectSum.of _ n alpha) (DirectSum.of _ m beta) =
      DirectSum.of (fun d : ℤ ↦ RelativeChow (fun _ ↦ 0) (pullback fY fZ) d) (n + m - r)
        (ChowGroup.intersectionProductOver X fY fZ r D alpha beta) := sorry

/-- The bilinear intersection product on total Chow homology over a smooth scheme.
Each homogeneous exterior product is capped with every relevant diagonal Gysin coefficient.
Coefficients beyond its nonnegative degree bound land in negative Chow groups, which vanish
over a field. The explicit deformation datum is a chosen model of deformation to the normal
cone; canonical production of that model is a library follow-up. -/
noncomputable def intersectionProductOverOfRankLoci (X : SchemeOverField k)
    [Smooth X.hom] {Y Z : SchemeOverField k} (fY : Y ⟶ X) (fZ : Z ⟶ X)
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    [LocallyOfFiniteType fY.left] [LocallyOfFiniteType fZ.left]
    (D : DiagonalSpecializationOfRankLoci X) :
    Total (fun _ ↦ 0) Y →+ Total (fun _ ↦ 0) Z →+ Total (fun _ ↦ 0) (pullback fY fZ) :=
  DirectSum.toAddMonoid fun n ↦
    AddMonoidHom.flip <| DirectSum.toAddMonoid fun m ↦
      AddMonoidHom.flip <|
        ∑ r ∈ Finset.range ((n + m).toNat + 1),
          ((Dedekind.Total.cap (fun _ ↦ 0) (diagonalGysinClassOfRankLoci X D r)
              (Dedekind.fiberProductToBase fY fZ) (Dedekind.fiberProductToProduct fY fZ)
              (prod.map fY fZ) (Dedekind.intersectionSquare_isPullback fY fZ)).comp
            (DirectSum.of (fun d : ℤ ↦ RelativeChow (fun _ ↦ 0) (Y ⨯ Z) d)
              (n + m))).compHom.comp (exteriorProductPairing Y Z n m)

/-- On homogeneous classes, the rank-locus intersection product is the finite sum of
Gysin caps in degrees `n + m - r`. -/
theorem intersectionProductOverOfRankLoci_of (X : SchemeOverField k)
    [Smooth X.hom] {Y Z : SchemeOverField k} (fY : Y ⟶ X) (fZ : Z ⟶ X)
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    [LocallyOfFiniteType fY.left] [LocallyOfFiniteType fZ.left]
    (D : DiagonalSpecializationOfRankLoci X) {n m : ℤ}
    (alpha : RelativeChow (fun _ ↦ 0) Y n)
    (beta : RelativeChow (fun _ ↦ 0) Z m) :
    intersectionProductOverOfRankLoci X fY fZ D (DirectSum.of _ n alpha)
        (DirectSum.of _ m beta) =
      ∑ r ∈ Finset.range ((n + m).toNat + 1),
        DirectSum.of (fun d : ℤ ↦ RelativeChow (fun _ ↦ 0) (pullback fY fZ) d)
          (n + m - r)
          ((diagonalGysinClassOfRankLoci X D r).cap (Dedekind.fiberProductToBase fY fZ)
            (Dedekind.fiberProductToProduct fY fZ) (prod.map fY fZ)
            (Dedekind.intersectionSquare_isPullback fY fZ) (n + m)
            (exteriorProductPairing Y Z n m alpha beta)) := sorry

/-- When the diagonal conormal sheaf has constant rank, the rank-locus intersection
product equals the fixed-rank intersection product. -/
theorem intersectionProductOverOfRankLoci_eq_ofRank (X : SchemeOverField k)
    [Smooth X.hom] {Y Z : SchemeOverField k} (fY : Y ⟶ X) (fZ : Z ⟶ X)
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    [LocallyOfFiniteType fY.left] [LocallyOfFiniteType fZ.left]
    (r : ℕ) [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecializationOfRankLoci X) :
    intersectionProductOverOfRankLoci X fY fZ D =
      intersectionProductOver X fY fZ r D := sorry

/-- The rank-locus intersection product is independent of the chosen model of deformation
to the normal cone of the diagonal. -/
theorem intersectionProductOverOfRankLoci_independent (X : SchemeOverField k)
    [Smooth X.hom] {Y Z : SchemeOverField k} (fY : Y ⟶ X) (fZ : Z ⟶ X)
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    [LocallyOfFiniteType fY.left] [LocallyOfFiniteType fZ.left]
    (D D' : DiagonalSpecializationOfRankLoci X) :
    intersectionProductOverOfRankLoci X fY fZ D =
      intersectionProductOverOfRankLoci X fY fZ D' := sorry

/-- Intersection products over a smooth scheme over a field are associative after the
canonical fiber-product associator, with no global dimension or rank assumption.
The explicit datum is a chosen model of deformation to the normal cone of the diagonal;
canonical production of this model is a library follow-up. -/
theorem intersectionProductOver_assocOfRankLoci
    (X : SchemeOverField k) [Smooth X.hom] {Y Z W : SchemeOverField k}
    (fY : Y ⟶ X) (fZ : Z ⟶ X) (fW : W ⟶ X)
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType W.hom]
    [LocallyOfFiniteType fY.left] [LocallyOfFiniteType fZ.left] [LocallyOfFiniteType fW.left]
    (D : DiagonalSpecializationOfRankLoci X)
    (alpha : Total (fun _ ↦ 0) Y) (beta : Total (fun _ ↦ 0) Z)
    (gamma : Total (fun _ ↦ 0) W) :
    map (fun _ ↦ 0) (pullbackAssoc fY fZ fZ fW).hom
        (intersectionProductOverOfRankLoci X (pullback.snd fY fZ ≫ fZ) fW D
          (intersectionProductOverOfRankLoci X fY fZ D alpha beta) gamma) =
      intersectionProductOverOfRankLoci X fY (pullback.fst fZ fW ≫ fZ) D alpha
        (intersectionProductOverOfRankLoci X fZ fW D beta gamma) := sorry

/-- Intersection products over a smooth scheme with constant diagonal conormal rank
are associative after the canonical fiber-product associator. -/
theorem intersectionProductOver_assoc
    (X : SchemeOverField k) [Smooth X.hom] {Y Z W : SchemeOverField k}
    (fY : Y ⟶ X) (fZ : Z ⟶ X) (fW : W ⟶ X)
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom] [LocallyOfFiniteType W.hom]
    [LocallyOfFiniteType fY.left] [LocallyOfFiniteType fZ.left] [LocallyOfFiniteType fW.left]
    (r : ℕ) [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecialization X r)
    (alpha : Total (fun _ ↦ 0) Y) (beta : Total (fun _ ↦ 0) Z)
    (gamma : Total (fun _ ↦ 0) W) :
    map (fun _ ↦ 0) (pullbackAssoc fY fZ fZ fW).hom
        (intersectionProductOver X (pullback.snd fY fZ ≫ fZ) fW r D
          (intersectionProductOver X fY fZ r D alpha beta) gamma) =
      intersectionProductOver X fY (pullback.fst fZ fW ≫ fZ) r D alpha
        (intersectionProductOver X fZ fW r D beta gamma) := sorry

end Total

end AlgebraicGeometry.ChowGroup
