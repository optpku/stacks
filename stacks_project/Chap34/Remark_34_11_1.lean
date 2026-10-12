/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Standard
import StacksCheckRecall

universe u v

/- Remark 34.11.1: restricting any chosen big fppf site to a standard scheme
precoverage gives a chosen site on the same presentation. -/
@[stacks 03FF] #check
  (AlgebraicGeometry.ChosenBigSite.standardSite :
    (X : AlgebraicGeometry.ChosenBigSite.{u, v}
      AlgebraicGeometry.Scheme.fppfPrecoverage) →
      (τ : AlgebraicGeometry.StandardTopology) →
        AlgebraicGeometry.ChosenBigSite.{u, v}
          (AlgebraicGeometry.StandardTopology.precoverage τ))

#check
  (AlgebraicGeometry.ChosenBigSite.standardSite_carrier :
    ∀ (X : AlgebraicGeometry.ChosenBigSite.{u, v}
      AlgebraicGeometry.Scheme.fppfPrecoverage) (τ : AlgebraicGeometry.StandardTopology),
      (AlgebraicGeometry.ChosenBigSite.standardSite X τ).carrier = X.carrier)

#check
  (AlgebraicGeometry.ChosenBigSite.standardSite_seedSchemes :
    ∀ (X : AlgebraicGeometry.ChosenBigSite.{u, v}
      AlgebraicGeometry.Scheme.fppfPrecoverage) (τ : AlgebraicGeometry.StandardTopology),
      (AlgebraicGeometry.ChosenBigSite.standardSite X τ).seedSchemes = X.seedSchemes)

#check
  (AlgebraicGeometry.ChosenBigSite.standardSite_pretopology_le :
    ∀ (X : AlgebraicGeometry.ChosenBigSite.{u, v}
      AlgebraicGeometry.Scheme.fppfPrecoverage) (τ : AlgebraicGeometry.StandardTopology),
      (AlgebraicGeometry.ChosenBigSite.standardSite X τ).pretopology ≤ X.pretopology)

#check
  (AlgebraicGeometry.ChosenBigSite.standardSite_toGrothendieck_le :
    ∀ (X : AlgebraicGeometry.ChosenBigSite.{u, v}
      AlgebraicGeometry.Scheme.fppfPrecoverage) (τ : AlgebraicGeometry.StandardTopology),
      (AlgebraicGeometry.ChosenBigSite.standardSite X τ).toGrothendieck ≤ X.toGrothendieck)

#check
  (AlgebraicGeometry.Scheme.zariskiTopology :
    CategoryTheory.GrothendieckTopology AlgebraicGeometry.Scheme.{u})

#check
  (AlgebraicGeometry.Scheme.etaleTopology :
    CategoryTheory.GrothendieckTopology AlgebraicGeometry.Scheme.{u})

#check
  (AlgebraicGeometry.Scheme.fppfTopology :
    CategoryTheory.GrothendieckTopology AlgebraicGeometry.Scheme.{u})

#check
  (AlgebraicGeometry.Scheme.bigSmoothSite :
    CategoryTheory.GrothendieckTopology AlgebraicGeometry.Scheme.{u})

#check
  (AlgebraicGeometry.Scheme.bigSyntomicSite :
    CategoryTheory.GrothendieckTopology AlgebraicGeometry.Scheme.{u})
