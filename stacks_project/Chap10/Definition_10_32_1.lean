/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.LocallyNilpotent
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.32.1

Locally nilpotent and nilpotent ideals are already owned by ReasLib and mathlib;
this chapter file preserves the source-facing labels as direct recalls.

@stack 00IL
-/

universe u

/- Definition 10.32.1 (1): an ideal `I` of a ring `R` is locally nilpotent when every
`x ∈ I` is nilpotent. The canonical owner is `Ideal.IsLocallyNilpotent`; the source
elementwise criterion is `Ideal.isLocallyNilpotent_iff`. -/
@[stacks 00IL "(1)"]
#check @Ideal.IsLocallyNilpotent
@[stacks 00IL "(1), elementwise criterion"]
#check @Ideal.isLocallyNilpotent_iff

section
variable {R : Type u} [CommSemiring R]

/- Definition 10.32.1 (2): an ideal `I` of a ring `R` is nilpotent when some power
`I ^ n` equals `0`. This is the generic mathlib predicate `IsNilpotent` specialized
to `Ideal R`. -/
@[stacks 00IL "(2)"]
#check (IsNilpotent : Ideal R → Prop)

end
