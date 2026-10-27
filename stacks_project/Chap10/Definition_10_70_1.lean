/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.ReesAlgebra.BlowupChart
import StacksCheckRecall

@[expose] public section

/-!
## Definition 10.70.1 (052Q)

@stack 052Q

The blowup algebra is the canonical mathlib Rees algebra `reesAlgebra I`.
Its explicit grading by the powers `I ^ n` and the affine chart `R[I / a]`
are owned by `ReasLib.RingTheory.ReesAlgebra`; this chapter entry is a
source-facing recall facade.
-/

universe u

/- Definition 10.70.1 (1): the Rees algebra of `I` is graded by the powers
`I ^ n`. -/
@[stacks 052Q "(1), Rees algebra"]
#check (reesAlgebra :
  {R : Type u} → [CommRing R] → (I : Ideal R) → Subalgebra R (Polynomial R))

/- Definition 10.70.1 (1): the degree-`n` piece is the image of `I ^ n`
under the degree-`n` monomial inclusion. -/
@[stacks 052Q "(1), Rees grading"]
#check (ReesAlgebra.Grading.grade :
  {R : Type u} → [CommRing R] → (I : Ideal R) → (n : ℕ) →
    Submodule R (reesAlgebra I))

/- Definition 10.70.1 (1): an element `a : I` determines the degree-one
Rees element `a t`. -/
@[stacks 052Q "(1), degree-one piece"]
#check (ReesAlgebra.Grading.degreeOne :
  {R : Type u} → [CommRing R] → (I : Ideal R) → (a : I) → reesAlgebra I)

/- Definition 10.70.1 (2): `R[I / a]` is the degree-zero homogeneous
localization of the Rees algebra at the degree-one element determined by `a`. -/
@[stacks 052Q "(2), affine blowup algebra"]
#check (affineBlowupChart :
  {R : Type u} → [CommRing R] → (I : Ideal R) → (a : I) → Type u)
