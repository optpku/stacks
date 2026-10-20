/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.FormalFiber.GRing
import StacksCheckRecall

/-!
# Lemma 15.50.2

@stack 07PN
-/

@[expose] public section

/- Lemma 15.50.2, tag `07PN`: a Noetherian ring is a `G`-ring exactly when every formal
fiber attached to a pair of primes `q ≤ p` is geometrically regular over `κ(q)`. -/
@[stacks 07PN "prime-pair criterion for G-rings"]
#check @IsGRing.iff_forall_primePair

/- The reusable bridge identifies `G`-rings with `P`-rings for geometric regularity. -/
#check @IsGRing.iff_isPRing

/- For a local ring, the same owner is expressed directly through its formal fibers. -/
#check @IsGRing.iff_holdsOnFormalFibers

/- The canonical field-algebra property and its inferred permanence laws. -/
#check @FieldAlgebraProperty.geometricallyRegular
#check @FieldAlgebraProperty.geometricallyRegular.formalFiberLaws
