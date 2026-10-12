/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.PrincipalParts.BaseChange
import StacksCheckRecall

@[expose] public section

/-!
# Remark 10.133.7

@stack 09CP

Remark 10.133.7 (Tag 09CP): a commutative square of commutative rings and a
linear map of modules induce a map on modules of principal parts.

The reusable owner is `PrincipalParts.BaseChange.map`; its generator and
composition lemmas give the source-facing behavior without exposing a quotient
presentation.
-/

@[stacks 09CP "principal-parts base change"]
#check @PrincipalParts.BaseChange.map

#check @PrincipalParts.BaseChange.map_apply_universalDifferential
#check @PrincipalParts.BaseChange.map_id
#check @PrincipalParts.BaseChange.map_comp
