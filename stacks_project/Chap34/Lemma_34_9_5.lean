/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc.Stability
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over
open AlgebraicGeometry

universe u v w

/- Lemma 34.9.5: if each member of a family of morphisms to `T` is flat and the family admits a
refinement by an fpqc covering of `T`, then the original family is an fpqc covering of `T`. -/
@[stacks 03L8]
#check (AlgebraicGeometry.Scheme.fpqcCovering_of_flat_of_exists_refinement :
  ∀ {T : Scheme.{u}} {ι : Type v},
    (X : ι → Over T) →
      (∀ i : ι, Flat (X i).hom) →
        (∃ (κ : Type w) (Y : κ → Over T),
          IsFpqcCovering Y ∧
            Refines
              (ofArrows (fun j ↦ (Y j).left) fun j ↦ (Y j).hom)
              (ofArrows (fun i ↦ (X i).left) fun i ↦ (X i).hom)) →
          IsFpqcCovering X)
