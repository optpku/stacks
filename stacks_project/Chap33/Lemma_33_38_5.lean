/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.GloballyGenerated
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 33.38.5: let `X` be a quasi-compact scheme. If every point lies in an affine
`Invertible.sectionNonvanishingOpen` of a globally generated invertible module, then `X` has an
ample invertible sheaf. -/
@[stacks 09NC]
#check
  (AlgebraicGeometry.Scheme.Modules.hasAmpleInvertibleModule_of_globallyGenerated_affineNonvanishingCover :
    ∀ {X : Scheme.{u}} [CompactSpace X],
      (∀ x : X, ∃ (L : X.Modules) (hL : AlgebraicGeometry.Scheme.Modules.Invertible L),
        SheafOfModules.IsGloballyGenerated L ∧
          ∃ s : Γ(L, ⊤), AlgebraicGeometry.Scheme.Modules.AffineOpenNeighborhood x
            (hL.sectionNonvanishingOpen s)) →
        AlgebraicGeometry.Scheme.Modules.HasAmpleInvertibleModule X)
