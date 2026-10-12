/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Curve.LocallyNoetherian

@[expose] public section

/-!
# Lemma 33.41.1 Canonical Recall

The shared curve-normalization API owns these statements.  This chapter file
keeps the source order and label without maintaining source-specific aliases.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Normalization.Curve

/- Lemma 33.41.1 (1): the normalization morphism of a one-dimensional locally Noetherian
scheme is integral. -/
@[stacks 0C45] #check
  (@AlgebraicGeometry.Scheme.Normalization.Curve.isIntegralTo :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X],
      topologicalKrullDim X = 1 → IsIntegralHom X.normalizationTo)

/- Lemma 33.41.1 (2): the normalization morphism of a one-dimensional locally Noetherian
scheme is surjective. -/
@[stacks 0C45]
#check
  (@AlgebraicGeometry.Scheme.Normalization.Curve.surjectiveTo :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X],
      topologicalKrullDim X = 1 → Surjective X.normalizationTo)

/- Lemma 33.41.1 (3): normalization induces a bijection on irreducible components. -/
@[stacks 0C45]
#check
  (@AlgebraicGeometry.Scheme.Normalization.Curve.normalizationTo_bijOn_irreducibleComponents :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X], topologicalKrullDim X = 1 →
      Set.BijOn (fun Z : Set X.normalization ↦ X.normalizationTo '' Z)
        (irreducibleComponents X.normalization) (irreducibleComponents X))

/- Lemma 33.41.1 (4): normalization factors through reduction. -/
@[stacks 0C45]
#check
  (@AlgebraicGeometry.Scheme.Normalization.Curve.factorsThroughReduction :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X], topologicalKrullDim X = 1 →
      ∃ νred : X.normalization ⟶ X.reduction,
        νred ≫ X.reductionι = X.normalizationTo)

/- Lemma 33.41.1 (5): the factor through reduction is the normalization of the reduction. -/
@[stacks 0C45]
#check
  (@AlgebraicGeometry.Scheme.Normalization.Curve.reductionFactorIsNormalization :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      (hdim : topologicalKrullDim X = 1) {νred : X.normalization ⟶ X.reduction},
      νred ≫ X.reductionι = X.normalizationTo →
        ∃ e : X.normalization ≅ X.reduction.normalization,
          νred = e.hom ≫ X.reduction.normalizationTo)

/- Lemma 33.41.1 (6): the factor through reduction is birational. -/
@[stacks 0C45]
#check
  (@AlgebraicGeometry.Scheme.Normalization.Curve.reductionFactorIsBirational :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      (hdim : topologicalKrullDim X = 1) {νred : X.normalization ⟶ X.reduction},
      νred ≫ X.reductionι = X.normalizationTo → IsBirational νred)

/- Lemma 33.41.1 (7): the normalization pushforward stalk at a closed point identifies with the
integral closure in the reduced total quotient ring. -/
@[stacks 0C45]
#check
  (@AlgebraicGeometry.Scheme.Normalization.Curve.pushforwardStalkEquivReducedIntegralClosure :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      (hdim : topologicalKrullDim X = 1) (x : X), x ∈ closedPoints X →
      ∃ e : Stalk.pushforward X x ≃+* Stalk.reducedIntegralClosure X x,
        e.toRingHom.comp (Stalk.pushforwardMap X x) =
          algebraMap (X.presheaf.stalk x) (Stalk.reducedIntegralClosure X x))

/- Lemma 33.41.1 (8): normalization fibers are finite. -/
@[stacks 0C45]
#check
  (@AlgebraicGeometry.Scheme.Normalization.Curve.fiberFinite :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      (hdim : topologicalKrullDim X = 1) (x : X),
      (X.normalizationTo.pointsOver x).Finite)

/- Lemma 33.41.1 (9): normalization has finite residue-field extensions. -/
@[stacks 0C45]
#check
  (@AlgebraicGeometry.Scheme.Normalization.Curve.residueFieldFinite :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      (hdim : topologicalKrullDim X = 1) (xν : X.normalization),
      Module.Finite (X.residueField (X.normalizationTo xν))
        (X.normalization.residueField xν))

/- Lemma 33.41.1 (10): normalization has a disjoint cover by integral normal locally
Noetherian opens. -/
@[stacks 0C45]
#check
  (@AlgebraicGeometry.Scheme.Normalization.Curve.existsDisjointOpenCover :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X], topologicalKrullDim X = 1 →
      ∃ (ι : Type u) (U : ι → X.normalization.Opens),
        TopologicalSpace.IsOpenCover U ∧
          Pairwise (fun i j ↦ Disjoint (U i : Set X.normalization)
            (U j : Set X.normalization)) ∧
            ∀ i, IsIntegral (U i).toScheme ∧
              (U i).toScheme.isNormal ∧ IsLocallyNoetherian (U i).toScheme)

/- Lemma 33.41.1 (11): affine opens of normalization are spectra of finite products of Dedekind
domains. -/
@[stacks 0C45]
#check
  (@AlgebraicGeometry.Scheme.Normalization.Curve.affineOpenIsoFiniteProductDedekind :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      (hdim : topologicalKrullDim X = 1) (U : X.normalization.affineOpens),
      ∃ (ι : Type u) (_hι : Finite ι) (R : ι → CommRingCat.{u})
        (e : (U : X.normalization.Opens).toScheme ≅ Spec (CommRingCat.of (Π i, R i))),
        ∀ i, IsDedekindDomain (R i))

end AlgebraicGeometry.Scheme.Normalization.Curve
