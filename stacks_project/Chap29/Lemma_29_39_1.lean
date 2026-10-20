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

/- Lemma 29.39.1: a relatively very ample module for a finite-type morphism to an affine scheme
is the pullback of the tautological module along an immersion over the base into a finite relative
projective space. -/
@[stacks 02NP] #check
  (AlgebraicGeometry.RelativelyVeryAmple.exists_projectiveSpaceImmersion_pullbackIso_of_finiteType_affineBase :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S} {L : X.Modules}
      [Scheme.Hom.FiniteType f] [IsAffine S] (hL : RelativelyVeryAmple f L),
      ∃ (n : ℕ) (P : ProjectiveSpaceOver S n) (i : X ⟶ P.scheme),
        ∃ e : (L ≅ (Scheme.Modules.pullback i).obj P.tautologicalSheaf),
          IsImmersion i ∧ i ≫ P.hom = f)
