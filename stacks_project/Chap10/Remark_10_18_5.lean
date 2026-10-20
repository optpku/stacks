/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import StacksCheckRecall

@[expose] public section

/-!
# Remark 10.18.5

@stack 00E6
-/

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Remark 10.18.5 is a core/canonical recall. The primitive fiber-ring object is
`p.asIdeal.Fiber S = κ(p) ⊗[R] S`, and the source-facing fiber of `Spec S → Spec R` over `p`
is canonically homeomorphic to its prime spectrum. -/
@[stacks 00E6 "spectrum fiber homeomorphism"]
#check @PrimeSpectrum.preimageHomeomorphFiber

/- Companion derived recall: the same fiber is nonempty exactly when the primitive fiber ring
`p.asIdeal.Fiber S` is nontrivial, equivalently when `p` lies in the image of `Spec S → Spec R`.
-/
@[stacks 00E6 "fiber nontriviality"]
#check @PrimeSpectrum.nontrivial_iff_mem_rangeComap

end
