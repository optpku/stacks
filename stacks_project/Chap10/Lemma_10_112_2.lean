/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.Spectrum.Maximal
import StacksCheckRecall

/-!
# Maximal Ideals Under Going Up

@stack 00OI
-/

@[expose] public section

/- Lemma 10.112.2 (Stacks tag `00OI`): for a ring map with the going-up
property, the inverse image of a maximal ideal is again maximal. -/
@[stacks 00OI]
#check @RingHom.isMaximal_comap_of_specializing
