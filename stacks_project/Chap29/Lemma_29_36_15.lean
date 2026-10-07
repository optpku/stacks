module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.LocalCriterion

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 29.36.15

For a locally finitely presented morphism of schemes and a point of its source, etaleness at
that point is equivalent to the nine local criteria stated in terms of the stalk map, residue
fibre, relative differentials, cotangent space, residue field, and affine presentations.
-/
@[stacks 02GU] #check
  (AlgebraicGeometry.Scheme.Hom.etaleAt_tfae_flat_stalkMap_fiber_differentials_standardEtale :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (x : X),
      List.TFAE
        [ f.EtaleAt x
        , AlgebraicGeometry.Scheme.Hom.flatStalkMapAndEtaleFiberAt f x
        , AlgebraicGeometry.Scheme.Hom.flatStalkMapAndUnramifiedFiberAt f x
        , AlgebraicGeometry.Scheme.Hom.flatStalkMapAndDifferentialsVanishAt f x
        , AlgebraicGeometry.Scheme.Hom.flatStalkMapAndCotangentSpaceVanishAt f x
        , AlgebraicGeometry.Scheme.Hom.flatStalkMapAndMaximalIdealResidueFieldAt f x
        , AlgebraicGeometry.Scheme.Hom.existsAffineOpenStandardSmoothRelativeDimensionZeroAt f x
        , AlgebraicGeometry.Scheme.Hom.existsAffineOpenJacobianPresentationRelativeDimensionZeroAt
            f x
        , ∃ V : S.affineOpens, f x ∈ (V : S.Opens) ∧
            ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
              f.IsStandardEtaleOver V U
        , AlgebraicGeometry.Scheme.Hom.existsAffineOpenStandardEtalePresentationAt f x
        ])
