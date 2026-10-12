/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Duality
import StacksCheckRecall

/-!
# Lemma 15.75.15 (07VI)

For a perfect object of `D(A)`, the canonical dual `RHom_A(K, A[0])` is perfect, the
bidual map is an isomorphism, and tensoring with the dual computes `RHom_A(K, -)` and
its degree-zero `Ext` comparison.  The reusable module-facing objects and comparison maps
are owned by `CategoryTheory.DerivedCategory.Perfect.Duality`; this file is the
source-facing recall surface.

@stack 07VI
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory
open CategoryTheory.DerivedCategory.Perfect

namespace CategoryTheory.DerivedCategory.Perfect.Duality

@[stacks 07VI "Lemma 15.75.15: canonical perfect derived dual"]
#check @dual

@[stacks 07VI "Lemma 15.75.15: contravariant dual map"]
#check @dualMap

@[stacks 07VI "Lemma 15.75.15: selected closed-owner derived dual"]
#check @selectedDual

@[stacks 07VI "Lemma 15.75.15: selected closed-owner dual map"]
#check @selectedDualMap

@[stacks 07VI "Lemma 15.75.15: perfect dual remains perfect"]
#check @IsPerfect.dual_isPerfect

@[stacks 07VI "Lemma 15.75.15: perfect objects are right-dualizable"]
#check @IsPerfect.isRightDualizable

@[stacks 07VI "Lemma 15.75.15: selected perfect dual"]
#check @IsPerfect.selectedDual_isPerfect

@[stacks 07VI "Lemma 15.75.15: bidual comparison"]
#check @bidualComparison

@[stacks 07VI "Lemma 15.75.15: bidual isomorphism for a perfect object"]
#check @bidualIso

@[stacks 07VI "Lemma 15.75.15: tensor/Hom comparison"]
#check @tensorComparison

@[stacks 07VI "Lemma 15.75.15: tensor/Hom comparison isomorphism"]
#check @tensorIso

@[stacks 07VI "Lemma 15.75.15: degree-zero tensor/Ext equivalence"]
#check @tensorExtZeroEquiv

end CategoryTheory.DerivedCategory.Perfect.Duality

end
