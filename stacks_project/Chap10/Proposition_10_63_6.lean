/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Filtration
import StacksCheckRecall

/-!
# Minimal support, associated, and filtration primes

@stack 02CE

Proposition 10.63.6 identifies the minimal points of a finite module's support, its associated
primes, and the prime factors of any prime filtration.  The three pairwise owner theorems below
give the source statement without a second bundled API.
-/

@[expose] public section

@[stacks 02CE "minimal associated-prime and support points"]
#check @associatedPrimes.minimal_point_iff_minimal_support

@[stacks 02CE "minimal support points and associated ideals"]
#check @minimal_support_iff_minimal_associatedPrimes

@[stacks 02CE "minimal filtration factors and associated-prime points"]
#check @Module.PrimeFiltration.minimal_primeFactor_iff_minimal_associatedPrimePoints
