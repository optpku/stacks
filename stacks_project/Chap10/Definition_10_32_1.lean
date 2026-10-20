module

public import ReasLib.RingTheory.Ideal.LocallyNilpotent
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.32.1

Locally nilpotent and nilpotent ideals are already owned by ReasLib and mathlib;
this chapter file preserves the source-facing labels as typed direct checks.

-/

universe u

section
variable {R : Type u} [CommRing R]

/- Definition 10.32.1: an ideal `I` of a ring `R` is locally nilpotent when every
`x ∈ I` has a vanishing natural-number power, and nilpotent when
`∃ n : ℕ, I ^ n = 0`. The canonical elementwise criterion for local nilpotence
is `Ideal.isLocallyNilpotent_iff`. -/
@[stacks 00IL]
#check (Ideal.isLocallyNilpotent_iff :
  ∀ I : Ideal R, I.IsLocallyNilpotent ↔ ∀ x ∈ I, ∃ n : ℕ, x ^ n = 0)

#check (Ideal.IsLocallyNilpotent : Ideal R → Prop)

/- An ideal is nilpotent when
`∃ n : ℕ, I ^ n = 0`. This is the generic mathlib predicate `IsNilpotent`
specialized to `Ideal R`. -/
#check (IsNilpotent : Ideal R → Prop)

end
