/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.H.Refinement
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over

universe u v

/- Lemma 38.34.5: an h covering of an affine scheme admits a finite affine refinement
arising from a proper surjective morphism of finite presentation. -/
@[stacks 0ETU] #check
  (AlgebraicGeometry.Scheme.HCovering.exists_standardPhRefinement :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsAffine X]
      {ι : Type v} (family : ι → Over X),
      AlgebraicGeometry.Scheme.HCovering family →
        ∃ cover : AlgebraicGeometry.StandardPhCovering X,
          AlgebraicGeometry.Scheme.Hom.FinitePresentation cover.toBase ∧
            Refines (ofArrows cover.obj cover.map)
              (ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom)))
