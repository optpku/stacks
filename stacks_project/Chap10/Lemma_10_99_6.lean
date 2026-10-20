/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Tor.FiniteLength
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.99.6
@stack 00MJ

The finite-length propagation statement is kept at the module-level `Tor₁`
interface. Composition-series and long-exact-sequence arguments are proof-stage infrastructure.
-/

@[stacks 00MJ "Tor-one vanishing for finite-length modules"]
#check @CategoryTheory.ModuleCat.Tor.isZero_one_of_finiteLength_of_residueField

@[stacks 00MJ "finite-length hypothesis"]
#check @IsFiniteLength

@[stacks 00MJ "degree-one Tor owner"]
#check @CategoryTheory.Tor
