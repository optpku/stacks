/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.Retraction

/-!
# Faithfully flat étale retractions

A commutative ring has the faithfully flat étale retraction property when every
faithfully flat étale algebra over it admits an algebra retraction. This
property passes to quotient rings.
-/

@[expose] public section

universe u

#check (Algebra.HasFaithfullyFlatEtaleRetraction : ∀ (R : Type u) [CommRing R], Prop)
