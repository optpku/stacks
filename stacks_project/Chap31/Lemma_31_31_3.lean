/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.Principality
import StacksCheckRecall

open AlgebraicGeometry

noncomputable section

universe u

open Set TopologicalSpace

/- Lemma 31.31.3: Let `R` be a Noetherian unique factorization domain. If a closed subscheme
`Z ⊆ ProjectiveSpace.scheme R n` has no embedded points and every irreducible component has
ambient codimension one, then its homogeneous twist ideal is principal. -/
@[stacks 0BXL] #check
  (AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.twistIdeal_isPrincipal_of_noEmbeddedPoints_of_codimensionOne :
    ∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
      [UniqueFactorizationMonoid R] (n : ℕ)
      (Z : (ProjectiveSpace.scheme R n).IdealSheafData)
      (P : ProjTwistPresentation (ProjectiveSpace.grading R n)),
      Z.subscheme.embeddedPoints = (∅ : Set Z.subscheme) →
        (∀ ξ : Z.subscheme, ξ ∈ genericPoints Z.subscheme →
          ringKrullDim ((ProjectiveSpace.scheme R n).presheaf.stalk
            (Z.subschemeι.base ξ)) = 1) →
          (AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.twistIdeal n Z P).toIdeal.IsPrincipal)
