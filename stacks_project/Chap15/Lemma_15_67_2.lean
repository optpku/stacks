/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude.FlatCokernel

/-!
# Flatness of the cutoff cokernel

@stack 0653

The reusable owner uses `CochainComplex.differentialCokernel`, the canonical form of the source's
incoming-differential cokernel.  Its finite-interval theorem matches the textbook hypotheses;
the lower-bound-only result is retained as a stronger companion.
-/

@[expose] public section

open CategoryTheory

universe u

/- Lemma 15.67.2 (0653): a bounded-above termwise-flat complex with Tor-amplitude in `[a,b]`
has flat incoming-differential cokernel in degree `a`. -/
@[stacks 0653 "flat differential cokernel from finite Tor amplitude"]
#check fun {R : Type u} [CommRing R] (E : CochainComplex (ModuleCat R) ℤ) (a b : ℤ)
    (hbounded : CochainComplex.minus (ModuleCat R) E) (hFlat : E.IsTermwiseFlat)
    (hTor : DerivedCategory.HasTorAmplitudeIn R (DerivedCategory.Q.obj E) a b) ↦
  (DerivedCategory.FlatCokernel.ofTorAmplitudeIn_cokernel E a b hbounded hFlat hTor :
    Module.Flat R (E.differentialCokernel a))

/- A lower Tor-amplitude bound already implies the same conclusion. -/
#check @CategoryTheory.DerivedCategory.FlatCokernel.ofTorAmplitudeGE
#check @CategoryTheory.DerivedCategory.FlatCokernel.ofTorAmplitudeGE_cokernel

/- The canonical homological object is opcycles, identified with the differential cokernel by a
named isomorphism. -/
#check @CategoryTheory.DerivedCategory.FlatCokernel.ofTorAmplitudeIn
#check @CochainComplex.opcyclesIsoCokernel
