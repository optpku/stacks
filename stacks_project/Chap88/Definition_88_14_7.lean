/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.LocalizationAway
public import ReasLib.RingTheory.Topology.Adic.Complete
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 88.14.7: let `A` be an adic topological ring which has a finitely
generated ideal of definition. Let `f ∈ A`. The completed principal localization
of `A` at `f` is `completedPrincipalLocalization I f`, the completion of
`Localization.Away f` (the principal localization `A_f = A[1/f]`) with respect to
any ideal of definition `I` of `A`. -/
@[stacks 0GGE]
#check (completedPrincipalLocalization : ∀ {A : Type u} [CommRing A], Ideal A → A → Type u)
