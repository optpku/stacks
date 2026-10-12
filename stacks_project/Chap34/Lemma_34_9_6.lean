/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc.Stability
import StacksCheckRecall

universe u v w

/-
Lemma 34.9.6: a pointwise flat family of scheme morphisms is fpqc-covering if it
becomes fpqc-covering after base change along every member of an fpqc covering.
-/
@[stacks 03L9] #check
  (AlgebraicGeometry.Scheme.fpqcCovering_of_flat_of_exists_covering_pullbacks :
    ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
      (X : ι → CategoryTheory.Over T),
      (∀ i : ι, AlgebraicGeometry.Flat (X i).hom) →
        (∃ (κ : Type w) (Y : κ → CategoryTheory.Over T),
          AlgebraicGeometry.Scheme.FpqcCovering Y ∧
            ∀ j : κ,
              AlgebraicGeometry.Scheme.FpqcCovering
                (fun i : ι ↦ CategoryTheory.Over.mk
                  (CategoryTheory.Limits.pullback.fst (Y j).hom (X i).hom))) →
          AlgebraicGeometry.Scheme.FpqcCovering X)
