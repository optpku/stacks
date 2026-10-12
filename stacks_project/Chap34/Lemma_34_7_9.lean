/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.ChosenPresentation
import StacksCheckRecall

universe u v

/- Lemma 34.7.9: for a scheme `S` in a chosen big fppf site, the big affine
fppf site over `S` is a site. -/
@[stacks 021T] #check
  (AlgebraicGeometry.ChosenBigFppfSite.bigAffineTopology.{u, v} :
    (X : AlgebraicGeometry.ChosenBigFppfSite.{u, v}) →
      (S : X.carrier) →
        CategoryTheory.GrothendieckTopology
          (AlgebraicGeometry.ChosenBigFppfSite.bigAffineSite X S))
