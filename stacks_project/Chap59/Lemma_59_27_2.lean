/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc.Comparison

universe u

/- Lemma 59.27.2: Any étale covering is an fpqc covering. -/
@[stacks 03PH] #check
  (AlgebraicGeometry.Scheme.Cover.fpqcCovering_of_etale :
    ∀ {T : AlgebraicGeometry.Scheme.{u}}
      (cover : AlgebraicGeometry.Scheme.Cover
        AlgebraicGeometry.Scheme.etalePrecoverage T),
      AlgebraicGeometry.Scheme.FpqcCovering
        (fun i : cover.I₀ ↦ CategoryTheory.Over.mk (cover.f i)))
