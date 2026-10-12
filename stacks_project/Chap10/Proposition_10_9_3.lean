/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.Defs
import StacksCheckRecall

@[expose] public section

/-!
# Proposition 10.9.3

@stack 00CP
-/

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v

variable {A : Type u} [CommRing A]
variable (S : Submonoid A)
variable {B : Type v} [CommRing B]

/- Domain triage:
* source-facing clauses: the universal property of the localization map `A → Localization S`.
* core/canonical owner: `IsLocalization`.
* primitive data: the localization instance and `algebraMap A (Localization S)`.
* derived API used here: `IsLocalization.lift`, `IsLocalization.lift_comp`,
  `IsLocalization.ringHom_ext`, and `IsLocalization.lift_unique`.
-/

/- Proposition 10.9.3 (1): if `f : A →+* B` sends every element of `S` to a unit, then the
universal property of localization is exactly the canonical owner construction
`IsLocalization.lift`. -/
@[stacks 00CP "localization lift"]
#check @IsLocalization.lift

/- Proposition 10.9.3 (2): the canonical lift commutes with the localization map. This is exactly
`IsLocalization.lift_comp`. -/
@[stacks 00CP "lift compatibility"]
#check @IsLocalization.lift_comp

/-
Companion recall: equality of ring homomorphisms out of a localization is already controlled by
precomposition with the localization map.
-/
@[stacks 00CP "localization extensionality"]
#check @IsLocalization.ringHom_ext

/- Proposition 10.9.3 (3): any ring homomorphism `Localization S →+* B` agreeing with `f` after
precomposition with the localization map is equal to the canonical lift. This is exactly
`IsLocalization.lift_unique`. -/
@[stacks 00CP "lift uniqueness"]
#check @IsLocalization.lift_unique

end
