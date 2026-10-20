/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.PullbackAdjunction.Surjective
import StacksCheckRecall

/-!
# Lemma 15.6.4

The adjunction and the invertibility of its counit are the canonical shared owners specialized to
the surjective ring-pullback situation.

@stack 07RU
-/

@[expose] public section

open CategoryTheory

universe u

noncomputable section

variable {B A A' : Type u} [CommRing B] [CommRing A] [CommRing A']
variable (S : SurjectiveRingPullbackSituation B A A')

/- Lemma 15.6.4 (1): the canonical module base-change functor has the fibre-product right
adjoint. -/
@[stacks 07RU "(1), fibre-product module adjunction"]
#check (ModuleCat.Pullback.adjunction S.bprimeToB S.bprimeToAprime S.comm)

/- Lemma 15.6.4 (2): for a surjective ring-pullback square, the counit of the fibre-product
module adjunction is an isomorphism. -/
@[stacks 07RU "(2), the adjunction counit is an isomorphism"]
#check (ModuleCat.Pullback.counit_isIso S)
