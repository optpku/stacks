/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Lemma_42_64_2_Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 42.64.2 (1): over a locally Dedekind base, if `X` is smooth over `S` and
equidimensional of `δ`-dimension `d = r + 1`, the map `A^p(X) → CH_(d - p)(X)`,
`c ↦ c ∩ [X]_d`, is an additive isomorphism. -/
@[stacks 0FCB] #check @AlgebraicGeometry.BivariantClass.Dedekind.capFundamentalEquiv

/- Lemma 42.64.2 (2): via this isomorphism, composition of bivariant classes
turns into the intersection product of Lemma 42.64.1. -/
@[stacks 0FCB] #check
  (AlgebraicGeometry.ChowGroup.Dedekind.capFundamental_mul :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.UniversallyCatenary S]
      [S.HasRingPropertyLocally
        (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
      (δ : S → ℤ) [IsDimensionFunction δ]
      (h_delta : ∀ s : S,
        δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
      {X : Over S}
      [AlgebraicGeometry.Smooth X.hom]
      (e : AlgebraicGeometry.Scheme.Modules.dual
        (AlgebraicGeometry.Scheme.Hom.normalSheaf
          (AlgebraicGeometry.ChowGroup.Dedekind.diagonal X).left) ≅
        AlgebraicGeometry.Scheme.Hom.conormalSheaf
          (AlgebraicGeometry.ChowGroup.Dedekind.diagonal X).left)
      (D : AlgebraicGeometry.ChowGroup.Dedekind.DiagonalSpecialization δ X e)
      (r : ℕ)
      [AlgebraicGeometry.Scheme.Hom.RelativeDimension X.hom r]
      [AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank r
        (AlgebraicGeometry.Scheme.Hom.conormalSheaf
          (AlgebraicGeometry.ChowGroup.Dedekind.diagonal X).left)]
      (p q : ℤ)
      (c : AlgebraicGeometry.ChowCohomology.degree δ X.hom p)
      (c' : AlgebraicGeometry.ChowCohomology.degree δ X.hom q),
      AlgebraicGeometry.ChowGroup.Dedekind.intersectionProductSelf
          δ h_delta e D r
          (DirectSum.of (fun d : ℤ ↦ AlgebraicGeometry.RelativeChow δ X d)
            ((r : ℤ) + 1 - p)
            (AlgebraicGeometry.BivariantClass.Dedekind.capFundamentalEquiv
              δ h_delta X r p c))
          (DirectSum.of (fun d : ℤ ↦ AlgebraicGeometry.RelativeChow δ X d)
            ((r : ℤ) + 1 - q)
            (AlgebraicGeometry.BivariantClass.Dedekind.capFundamentalEquiv
              δ h_delta X r q c')) =
        DirectSum.of (fun d : ℤ ↦ AlgebraicGeometry.RelativeChow δ X d)
          ((r : ℤ) + 1 - (p + q))
          (AlgebraicGeometry.BivariantClass.Dedekind.capFundamentalEquiv
            δ h_delta X r (p + q)
            (AlgebraicGeometry.ChowCohomology.mul δ X.hom c c')))
