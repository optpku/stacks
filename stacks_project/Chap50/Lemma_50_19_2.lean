/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.TraceRule

universe u

@[expose] public section

/- Lemma 50.19.2: there is a unique degreewise trace rule for finite syntomic morphisms,
normalized by the structure-sheaf trace and compatible with arbitrary cartesian base change. -/
@[stacks 0FLB] #check
  (AlgebraicGeometry.Scheme.RelativeDifferentials.existsUniqueTraceRule.{u} :
    ∃! r : AlgebraicGeometry.Scheme.RelativeDifferentials.TraceRule.{u},
      AlgebraicGeometry.Scheme.RelativeDifferentials.IsTraceRule r)
