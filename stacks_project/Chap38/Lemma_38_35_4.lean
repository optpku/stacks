/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.H.Sheaf
import StacksCheckRecall

universe u

open CategoryTheory

/- Lemma 38.35.4: an h-sheaf on a sufficiently large full subcategory of
schemes over `S` that preserves directed affine limits extends to all schemes
over `S`, where it remains an h-sheaf and preserves directed affine limits. -/
@[stacks 0EV3] #check
  (AlgebraicGeometry.Scheme.Over.Extension.existsHSheafExtension :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (C : CategoryTheory.ObjectProperty (CategoryTheory.Over S))
      (F : C.FullSubcategoryᵒᵖ ⥤ Type (u + 1))
      (hC_open : AlgebraicGeometry.Scheme.Over.Extension.ContainsAffineOpens C)
      (hC_fp : AlgebraicGeometry.Scheme.Over.Extension.ContainsFinitelyPresentedAffines C)
      (hF_h : CategoryTheory.Presheaf.IsSheaf
        (C.ι.restrictedTopology
          ((AlgebraicGeometry.Scheme.hPrecoverage.toGrothendieck).over S)) F)
      (hF_limits :
        AlgebraicGeometry.Scheme.Over.Extension.PreservesDirectedAffineLimits C F),
      ∃ (F' : (CategoryTheory.Over S)ᵒᵖ ⥤ Type (u + 1)),
        ∃ (eF' : C.ι.op ⋙ F' ≅ F),
          CategoryTheory.Presheaf.IsSheaf
              ((AlgebraicGeometry.Scheme.hPrecoverage.toGrothendieck).over S) F' ∧
            AlgebraicGeometry.Scheme.Over.PreservesDirectedAffineLimits S F')
