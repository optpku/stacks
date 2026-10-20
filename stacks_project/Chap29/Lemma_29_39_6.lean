/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery.ProjectiveSpace

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.39.6: let `f : X ⟶ S` be a finite-type morphism of schemes and let
`𝓛` be an invertible sheaf on `X`. Then `𝓛` is `f`-relatively very ample if and
only if there is an open cover `S = ⋃ V_j` such that, for every `j`, the inverse-image open
`X_j = f^{-1}(V_j)` admits an immersion over `V_j` into projective space
`projectiveSpace V_j n_j` and the restriction of `𝓛` to `X_j` is isomorphic to the
pullback of the tautological sheaf `𝒪(1)`. -/
@[stacks 02NQ] #check
  (AlgebraicGeometry.RelativelyVeryAmple.iff_exists_openCover_projectiveSpacePresentation_of_finiteType :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S} {L : X.Modules}
      [Scheme.Modules.Invertible L] [Scheme.Hom.FiniteType f],
      RelativelyVeryAmple f L ↔
        ∃ (ι : Type u) (V : ι → S.Opens), TopologicalSpace.IsOpenCover V ∧
          ∀ j : ι,
            ∃ (n : ℕ) (P : ProjectiveSpaceOver (V j).toScheme n)
              (i : (f ⁻¹ᵁ V j).toScheme ⟶ P.scheme),
              RelativelyVeryAmplePresentation (f ∣_ V j)
                (restrictToBasePreimage f L (V j)) P.hom
                (ProjectiveSpaceOver.standardModule (V j).toScheme n)
                P.isProjectiveBundle i)
