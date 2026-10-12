/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc.Coproduct
import StacksCheckRecall

universe u v

/-
Lemma 34.9.4: an indexed family of scheme morphisms is an fpqc covering if and only if the
singleton family formed by its induced coproduct morphism is an fpqc covering.
-/
@[stacks 040I] #check
  (AlgebraicGeometry.Scheme.fpqcCovering_iff_coproductSingleton :
    ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
      (X : ι → CategoryTheory.Over T)
      [CategoryTheory.Limits.HasCoproduct (fun i ↦ (X i).left)],
      AlgebraicGeometry.Scheme.FpqcCovering X ↔
        AlgebraicGeometry.Scheme.FpqcCovering
          (CategoryTheory.Limits.FormalCoproduct.Over.coproductSingleton
            (CategoryTheory.Limits.FormalCoproduct.mk ι X)).obj)
