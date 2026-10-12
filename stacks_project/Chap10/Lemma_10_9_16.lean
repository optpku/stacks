/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.Ideal
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.9.16

@stack 02C9
-/

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {A : Type u} [CommRing A] (S : Submonoid A)

/- Lemma 10.9.16: every ideal `I'` of `Localization S` is the localization of its inverse image
in `A`, namely
`Ideal.map (algebraMap A (Localization S)) (Ideal.comap (algebraMap A (Localization S)) I') = I'`.
This is exactly the canonical theorem `IsLocalization.map_comap` specialized to ideals of
`Localization S`. -/
@[stacks 02C9]
#check (IsLocalization.map_comap S (Localization S))

end
