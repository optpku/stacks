/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialSet.Subcomplex.AdjoinSimplex
import StacksCheckRecall

/-!
@stack 018R

# Source-facing bridge for Lemma 14.21.7

The source-facing degreewise hypotheses are translated by
`SSet.Subcomplex.singleSimplex.Degreewise` into ReasLib's canonical missing-simplex and
attachment APIs.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

namespace SSet.Subcomplex.singleSimplex

variable {V : SSet.{u}} {U : V.Subcomplex} {n : ℕ} {x : V _⦋n⦌}
variable (h : Degreewise U n x)

/- Lemma 14.21.7: the degreewise hypotheses exhibit `V` as the canonical pushout obtained by
adjoining `x` to `U` along its boundary. -/
@[stacks 018R]
#check (h.isPushout :
  IsPushout ∂Δ[n].ι (h.simplex.boundaryMap h.boundary)
    (yonedaEquiv.symm x) U.ι)

#check h.spec
#check h.nonDegenerate
#check h.simplex
#check h.simplex_eq
#check h.boundary
#check h.adjoin_eq_top
#check h.attachment
#check h.attachment.isPushout

end SSet.Subcomplex.singleSimplex
