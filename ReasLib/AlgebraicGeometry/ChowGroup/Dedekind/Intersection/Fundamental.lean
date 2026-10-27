/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Dedekind.Fundamental
public import ReasLib.AlgebraicGeometry.ChowGroup.Dedekind.Intersection

/-!
# Fundamental-class cap and self-intersection

The total diagonal intersection product on a smooth scheme agrees with
composition of identity bivariant classes after capping with its fundamental class.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Set
open AlgebraicGeometry.Scheme.Hom
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.Dedekind

/-- The first projection from the identity fiber product `X ×_X X` to `X`. -/
noncomputable abbrev intersectionProductSelfTo {S : Scheme.{u}} (X : Over S) :
    pullback (𝟙 X) (𝟙 X) ⟶ X :=
  pullback.fst (𝟙 X) (𝟙 X)

/-- The comparison from the identity fiber product is its first projection. -/
theorem intersectionProductSelfTo_eq {S : Scheme.{u}} (X : Over S) :
    intersectionProductSelfTo X = pullback.fst (𝟙 X) (𝟙 X) := rfl

/-- The first projection from the identity fiber product is proper. -/
instance intersectionProductSelfTo_isProper {S : Scheme.{u}} (X : Over S) :
    IsProper (intersectionProductSelfTo X).left := sorry

/-- The self-intersection product on total Chow homology is the total diagonal
intersection product pushed forward from the identity fiber product.
Its presentation independence follows from `intersectionProductTotal_independent`. -/
noncomputable def intersectionProductSelf
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    {X : Over S} [LocallyOfFiniteType X.hom] [Smooth X.hom]
    (e : Scheme.Modules.dual (normalSheaf (diagonal X).left) ≅
      conormalSheaf (diagonal X).left)
    (D : DiagonalSpecialization δ X e) (alpha beta : Total δ X) :
    Total δ X :=
  Total.map δ (intersectionProductSelfTo X)
    (intersectionProductTotal δ h_delta (𝟙 X) (𝟙 X) e D alpha beta)

/-- The self-intersection product is computed by total diagonal intersection followed
by pushforward along the first projection of the identity fiber product. -/
theorem intersectionProductSelf_def
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    {X : Over S} [LocallyOfFiniteType X.hom] [Smooth X.hom]
    (e : Scheme.Modules.dual (normalSheaf (diagonal X).left) ≅
      conormalSheaf (diagonal X).left)
    (D : DiagonalSpecialization δ X e) (alpha beta : Total δ X) :
    intersectionProductSelf δ h_delta e D alpha beta =
      Total.map δ (intersectionProductSelfTo X)
        (intersectionProductTotal δ h_delta (𝟙 X) (𝟙 X) e D alpha beta) := rfl

/-- For a smooth equidimensional scheme over a dimension-one locally Dedekind base,
cap with the fundamental class turns composition of homogeneous identity bivariant
classes into the self-intersection product, for every diagonal deformation presentation. -/
theorem capFundamental_mul
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (h_dim : ∀ component : irreducibleComponents S, topologicalKrullDim component = 1)
    {X : Over S} [Smooth X.hom]
    (e : Scheme.Modules.dual (normalSheaf (diagonal X).left) ≅
      conormalSheaf (diagonal X).left)
    (D : DiagonalSpecialization δ X e) (d p q : ℤ)
    (hX : ∀ η : genericPoints X.left, X.hom.relativeDimensionFunction δ η.1 = d)
    (c : ChowCohomology.degree δ X.hom p)
    (c' : ChowCohomology.degree δ X.hom q) :
    intersectionProductSelf δ h_delta e D
        (DirectSum.of (fun k : ℤ ↦ RelativeChow δ X k) (d - p)
          (BivariantClass.Dedekind.capFundamental δ X d p c))
        (DirectSum.of (fun k : ℤ ↦ RelativeChow δ X k) (d - q)
          (BivariantClass.Dedekind.capFundamental δ X d q c')) =
      DirectSum.of (fun k : ℤ ↦ RelativeChow δ X k) (d - (p + q))
        (BivariantClass.Dedekind.capFundamental δ X d (p + q)
          (ChowCohomology.mul δ X.hom c c')) := sorry

end AlgebraicGeometry.ChowGroup.Dedekind
