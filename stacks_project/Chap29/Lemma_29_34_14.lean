/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.LocalCriterion

open AlgebraicGeometry

universe u

/- Lemma 29.34.14

For a locally finitely presented morphism, smoothness at a point is equivalent to the local
flatness, differential-generator, standard-smooth-chart, and Jacobian-presentation criteria.
-/
@[stacks 01V9] #check
  (AlgebraicGeometry.Scheme.Hom.smoothAt_tfae_flat_stalkMap_smoothFiber_differentials_standardSmooth :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (x : X),
      List.TFAE
        [ f.SmoothAt x
        , AlgebraicGeometry.Scheme.Hom.flatStalkMapAndSmoothFiberAt f x
        , AlgebraicGeometry.Scheme.Hom.flatStalkMapAndDifferentialsGeneratedAt f x
        , AlgebraicGeometry.Scheme.Hom.flatStalkMapAndCotangentSpaceGeneratedAt f x
        , AlgebraicGeometry.Scheme.Hom.existsAffineOpenStandardSmoothAt f x
        , AlgebraicGeometry.Scheme.Hom.existsAffineOpenJacobianPresentationAt f x
        ])
