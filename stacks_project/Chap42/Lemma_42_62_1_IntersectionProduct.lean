/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Restriction
public import ReasLib.AlgebraicGeometry.ChowGroup.ExteriorProduct
public import ReasLib.AlgebraicGeometry.ChowGroup.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Over
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Product
public import stacks_project.Chap42.Lemma_42_62_5_IntersectionProduct

/-!
# Intersection products of Chow classes over a smooth base

This file packages the section 42.62 product `α · β = Δ!(α × β)` for schemes
locally of finite type over a base `X`, using the comparison square of
`Y ×_X Z` against `Y ×_k Z` over the diagonal of `X`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules hiding dual

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The fiber product of two objects of `Over S` is locally of finite type over `S` when
both factors are. -/
instance locallyOfFiniteType_overPullback {S : Scheme.{u}} {X Y Z : Over S}
    (f : Y ⟶ X) (g : Z ⟶ X) [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom] :
    LocallyOfFiniteType (pullback f g).hom := sorry

namespace BivariantClass

/-- Assemble a bivariant class degreewise to a degree-shifting map on total Chow homology. -/
noncomputable def totalCap
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y X' Y' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    {f : X ⟶ Y} {p : ℤ} (c : BivariantClass delta f p)
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left) :
    ChowGroup.Total delta Y' →+ ChowGroup.Total delta X' :=
  DirectSum.toAddMonoid fun k ↦
    (DirectSum.of (fun d : ℤ ↦ RelativeChow delta X' d) (k - p)).comp
      (c.cap i f' g square k)

/-- Evaluation of `totalCap` on a homogeneous class is the corresponding cap in shifted
degree. -/
theorem totalCap_of
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y X' Y' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    {f : X ⟶ Y} {p : ℤ} (c : BivariantClass delta f p)
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left f.left g.left) (k : ℤ)
    (alpha : RelativeChow delta Y' k) :
    totalCap delta c i f' g square (DirectSum.of _ k alpha) =
      DirectSum.of (fun d : ℤ ↦ RelativeChow delta X' d) (k - p)
        (c.cap i f' g square k alpha) := sorry

end BivariantClass

namespace ChowGroup

variable {k : Type u} [Field k]

/-- The structure morphism of `Y ×_X Z` over `X`. -/
noncomputable def intersectionSquare_fst {X Y Z : SchemeOverField k}
    (fY : Y ⟶ X) (fZ : Z ⟶ X) :
    pullback fY fZ ⟶ X :=
  pullback.fst fY fZ ≫ fY

/-- The comparison morphism `Y ×_X Z ⟶ Y ×_k Z`. -/
noncomputable def intersectionSquare_toProduct {X Y Z : SchemeOverField k}
    (fY : Y ⟶ X) (fZ : Z ⟶ X) :
    pullback fY fZ ⟶ Y ⨯ Z :=
  prod.lift (pullback.fst fY fZ) (pullback.snd fY fZ)

/-- The comparison square identifying `Y ×_X Z` with the pullback of `Y ×_k Z` along
the diagonal of `X`. -/
theorem intersectionSquare_isPullback {X Y Z : SchemeOverField k}
    (fY : Y ⟶ X) (fZ : Z ⟶ X) :
    IsPullback (intersectionSquare_fst fY fZ).left
      (intersectionSquare_toProduct fY fZ).left (diagonal X).left (prod.map fY fZ).left := sorry

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
  (diagonalGysinClass X r D).cap (intersectionSquare_fst fY fZ)
    (intersectionSquare_toProduct fY fZ) (prod.map fY fZ)
    (intersectionSquare_isPullback fY fZ) (n + m)
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
      (diagonalGysinClass X r D).cap (intersectionSquare_fst fY fZ)
        (intersectionSquare_toProduct fY fZ) (prod.map fY fZ)
        (intersectionSquare_isPullback fY fZ) (n + m)
        (exteriorProductPairing Y Z n m alpha beta) := sorry

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
  (BivariantClass.totalCap (fun _ ↦ 0) (diagonalGysinClass X r D)
      (intersectionSquare_fst fY fZ) (intersectionSquare_toProduct fY fZ)
      (prod.map fY fZ) (intersectionSquare_isPullback fY fZ)).compHom.comp
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
      BivariantClass.totalCap (fun _ ↦ 0) (diagonalGysinClass X r D)
        (intersectionSquare_fst fY fZ) (intersectionSquare_toProduct fY fZ)
        (prod.map fY fZ) (intersectionSquare_isPullback fY fZ)
        (exteriorProduct Y Z alpha beta) := sorry

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

end Total

end ChowGroup

end AlgebraicGeometry
