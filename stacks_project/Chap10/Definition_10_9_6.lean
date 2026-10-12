/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.9.6

@stack 07JZ
-/

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable (A : Type u) [CommSemiring A] (S : Submonoid A)
variable (M : Type v) [AddCommMonoid M] [Module A M]

/- Definition 10.9.6: for a commutative semiring `A`, a submonoid `S`, and an `A`-module `M`,
the localized module `S⁻¹M` is the canonical owner object `LocalizedModule S M`. -/
@[stacks 07JZ "localized module owner"]
#check @LocalizedModule

/- Companion recall: the canonical localization map `M → S⁻¹M` is the linear map
`LocalizedModule.mkLinearMap S M`. -/
@[stacks 07JZ "localized module map"]
#check @LocalizedModule.mkLinearMap

/- Companion recall: the canonical owner instance expressing that `LocalizedModule S M` is the
localization of `M` with respect to `S` is `localizedModuleIsLocalizedModule`. -/
@[stacks 07JZ "localized module universal property"]
#check @localizedModuleIsLocalizedModule

/- The canonical localization map sends `m` to the fraction `m / 1`. -/
@[stacks 07JZ "localized module map application"]
#check @LocalizedModule.mkLinearMap_apply

end
