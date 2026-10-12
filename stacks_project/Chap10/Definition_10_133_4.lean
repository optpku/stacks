/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.PrincipalParts.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.133.4

@stack 09CL

Definition 10.133.4 (Tag 09CL): the `k`-th principal-parts module of an
`S`-module `M` over `R` is the module constructed in Lemma 10.133.3.

The canonical owner is `PrincipalParts.module`.  Its universal map and
representing equivalence remain available as the useful downstream interface;
the textbook naming introduces no additional data.
-/

@[stacks 09CL "module of principal parts"]
#check @PrincipalParts.module

#check @PrincipalParts.universalDifferential
#check @PrincipalParts.representingEquiv
