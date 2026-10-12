/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.Extension
import StacksCheckRecall

@[expose] public section

universe u v

variable {A : Type u} [CommSemiring A] {I : Ideal A} (gamma : DividedPowers I)
variable {B : Type v} [CommSemiring B] (f : A →+* B)

/- Definition 23.4.1 (07H0): divided powers extend along a ring map when the image ideal admits
divided powers making that map a divided-power morphism. -/
@[stacks 07H0] #check (gamma.extendsAlong f : Prop)

#check @DividedPowers.Extension
#check @DividedPowers.extendsAlong_iff
#check @DividedPowers.extendsAlong_iff_nonempty_extension
