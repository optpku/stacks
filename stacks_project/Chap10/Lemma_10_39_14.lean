/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.39.14

@stack 00HO
-/

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Lemma 10.39.14 is a `bridge/view` restatement of the owner theorem
`Module.FaithfullyFlat.iff_zero_iff_rTensor_zero`: an `R`-module `M` is faithfully flat if and
only if it is flat and for every `R`-linear map `α : N →ₗ[R] N'`, one has `α = 0` exactly when
the induced map `LinearMap.rTensor M α` is zero. The source wording `α = 0 ↔ α ⊗ id_M = 0`
simply reverses the inner equivalence, so the main entry should be direct canonical recall. -/
@[stacks 00HO]
#check @Module.FaithfullyFlat.iff_zero_iff_rTensor_zero

end
