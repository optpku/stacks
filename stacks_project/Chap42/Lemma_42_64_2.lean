/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Dedekind.Fundamental
public import ReasLib.AlgebraicGeometry.ChowGroup.Dedekind.Intersection.Fundamental
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.BivariantClass.Dedekind
open AlgebraicGeometry.ChowGroup.Dedekind
open scoped DirectSum

noncomputable section

universe u

/- Lemma 42.64.2 (1): for a smooth scheme equidimensional of δ-dimension d over
 a dimension-one locally Dedekind base, capping with [X]d is bijective. -/
@[stacks 0FCB] #check (AlgebraicGeometry.BivariantClass.Dedekind.capFundamental_bijective :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (h_dim : ∀ component : irreducibleComponents S, topologicalKrullDim component = 1)
    (X : Over S) [Smooth X.hom] (d p : ℤ)
    (hX : ∀ η : genericPoints X.left, X.hom.relativeDimensionFunction δ η.1 = d),
    Function.Bijective (capFundamental δ X d p))

#check (AlgebraicGeometry.BivariantClass.Dedekind.capFundamental_zero :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (d p : ℤ),
    capFundamental δ X d p (ChowCohomology.zeroClass δ X.hom p) = 0)

#check (AlgebraicGeometry.BivariantClass.Dedekind.capFundamental_add :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (d p : ℤ)
    (c c' : ChowCohomology.degree δ X.hom p),
    capFundamental δ X d p (ChowCohomology.addClass δ X.hom c c') =
      capFundamental δ X d p c + capFundamental δ X d p c')

/- Lemma 42.64.2 (2): under the fundamental-class cap identification, composition
of bivariant classes is the diagonal intersection product. -/
@[stacks 0FCB] #check (AlgebraicGeometry.ChowGroup.Dedekind.capFundamental_mul :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S]
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
    (c' : ChowCohomology.degree δ X.hom q),
    intersectionProductSelf δ h_delta e D
        (DirectSum.of (fun k : ℤ ↦ RelativeChow δ X k) (d - p)
          (BivariantClass.Dedekind.capFundamental δ X d p c))
        (DirectSum.of (fun k : ℤ ↦ RelativeChow δ X k) (d - q)
          (BivariantClass.Dedekind.capFundamental δ X d q c')) =
      DirectSum.of (fun k : ℤ ↦ RelativeChow δ X k) (d - (p + q))
        (BivariantClass.Dedekind.capFundamental δ X d (p + q)
          (ChowCohomology.mul δ X.hom c c')))
