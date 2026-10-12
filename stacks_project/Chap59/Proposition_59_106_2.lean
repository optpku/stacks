/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Sites.H.EssentialImage
import StacksCheckRecall

open CategoryTheory hiding Square
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open CategoryTheory.GrothendieckTopology
open CategoryTheory.GrothendieckTopology.Derived
open CategoryTheory.GrothendieckTopology.Derived.Sections.MayerVietoris

universe u

/- Proposition 59.106.2: for a bounded-below derived object on the fppf site over
`S`, membership in the essential image of the h-to-fppf right-derived direct
image is equivalent to the Mayer–Vietoris condition on every affine almost
blowup square. -/
@[stacks 0EWQ] #check
  (AlgebraicGeometry.Scheme.H.essImage_iff_affineAlmostBlowupCondition :
    ∀ {S : Scheme.{u}}
      (K : DerivedCategory.Plus (SiteAbelianSheafCat (Scheme.fppfTopology.over S))),
      Functor.essImage (Absolute.rightDerived (AlgebraicGeometry.Scheme.H.fppf_le S))
          (DerivedCategory.Plus.ι.obj K) ↔
        ∀ (sq : Square (Over S)),
          AlgebraicGeometry.Scheme.H.IsAffineAlmostBlowupSquare sq →
          sq.Condition (Scheme.fppfTopology.over S) (DerivedCategory.Plus.ι.obj K))
