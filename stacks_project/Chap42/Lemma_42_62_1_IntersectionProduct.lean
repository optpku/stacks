/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Intersection.Over

/-!
# Compatibility API for intersection products over a field

The cap action and diagonal comparison square specialize the canonical general-base
constructions. Intersection products are provided by their mathematical owner.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules hiding dual

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The fiber product of two schemes locally of finite type over a field is locally of
finite type over that field. -/
instance locallyOfFiniteType_overPullback {k : Type u} [Field k]
    {X Y Z : SchemeOverField k} (fY : Y ⟶ X) (fZ : Z ⟶ X)
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom] :
    LocallyOfFiniteType (pullback fY fZ).hom :=
  ChowGroup.Dedekind.pullback_locallyOfFiniteType fY fZ

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
  ChowGroup.Dedekind.Total.cap delta c i f' g square

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
        (c.cap i f' g square k alpha) :=
  ChowGroup.Dedekind.Total.cap_of delta c i f' g square k alpha

end BivariantClass

namespace ChowGroup

variable {k : Type u} [Field k]

/-- The structure morphism of `Y ×_X Z` over `X`. -/
noncomputable def intersectionSquare_fst {X Y Z : SchemeOverField k}
    (fY : Y ⟶ X) (fZ : Z ⟶ X) :
    pullback fY fZ ⟶ X :=
  Dedekind.fiberProductToBase fY fZ

/-- The comparison morphism `Y ×_X Z ⟶ Y ×_k Z`. -/
noncomputable def intersectionSquare_toProduct {X Y Z : SchemeOverField k}
    (fY : Y ⟶ X) (fZ : Z ⟶ X) :
    pullback fY fZ ⟶ Y ⨯ Z :=
  Dedekind.fiberProductToProduct fY fZ

/-- The comparison square identifying `Y ×_X Z` with the pullback of `Y ×_k Z` along
the diagonal of `X`. -/
theorem intersectionSquare_isPullback {X Y Z : SchemeOverField k}
    (fY : Y ⟶ X) (fZ : Z ⟶ X) :
    IsPullback (intersectionSquare_fst fY fZ).left
      (intersectionSquare_toProduct fY fZ).left (diagonal X).left (prod.map fY fZ).left :=
  Dedekind.intersectionSquare_isPullback fY fZ

#check (AlgebraicGeometry.ChowGroup.Total.intersectionProductOver :
  ∀ (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] {Y Z : SchemeOverField k} (fY : Y ⟶ X) (fZ : Z ⟶ X)
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    [LocallyOfFiniteType fY.left] [LocallyOfFiniteType fZ.left] (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecialization X r),
    Total (fun _ ↦ 0) Y →+ Total (fun _ ↦ 0) Z →+ Total (fun _ ↦ 0) (pullback fY fZ))

end ChowGroup

end AlgebraicGeometry
