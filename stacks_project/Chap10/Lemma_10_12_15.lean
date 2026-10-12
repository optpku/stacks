/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.BaseChange
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.12.15

@stack 00DK
-/

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped TensorProduct

section

variable {R : Type u} [CommSemiring R]
variable {S : Submonoid R}
variable {M : Type v} [AddCommMonoid M] [Module R M]

/- Lemma 10.12.15 is a `bridge/view` item in the localization/base-change domain. The primitive
owner abstraction is `IsLocalizedModule.isBaseChange`, and the canonical derived comparison is
`LocalizedModule.equivTensorProduct`. The Stacks statement uses its symmetric orientation. -/

/- Lemma 10.12.15: the localized module `S⁻¹M` is canonically isomorphic to
`S⁻¹R ⊗[R] M`. This is the symmetric orientation of the owner equivalence
`LocalizedModule.equivTensorProduct`. -/
@[stacks 00DK "localization tensor equivalence"]
#check (LocalizedModule.equivTensorProduct S M).symm

/- The symmetric form of the canonical isomorphism sends `(a / s) ⊗ m` to `a • (m / s)`. -/
@[stacks 00DK "tensor generator formula"]
#check @LocalizedModule.equivTensorProduct_symm_apply_tmul

end
