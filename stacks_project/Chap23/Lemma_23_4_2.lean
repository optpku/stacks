/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.Extension.Criteria
import StacksCheckRecall

@[expose] public section

universe u v

section Uniqueness

variable {A : Type u} [CommSemiring A] {I : Ideal A}
variable (gamma : DividedPowers I) {B : Type v} [CommSemiring B]
variable (f : A →+* B)

/- Lemma 23.4.2 (1) (07H1): divided-power extension data along a fixed ring map are unique. -/
@[stacks 07H1 "(1)"]
#check (DividedPowers.subsingletonExtensions gamma f :
  Subsingleton (gamma.Extension f))

end Uniqueness

section Existence

variable {A : Type u} [CommRing A] {I : Ideal A}
variable (gamma : DividedPowers I) {B : Type v} [CommRing B]
variable (f : A →+* B)
variable (h : I.map f = ⊥ ∨ I.IsPrincipal ∨ f.Flat)

/- Lemma 23.4.2 (2) (07H1): extension exists when the image ideal is zero, the source ideal is
principal, or the ring map is flat. -/
@[stacks 07H1 "(2)"]
#check (DividedPowers.extendsAlong_of_map_eq_bot_or_isPrincipal_or_flat gamma f h :
  gamma.extendsAlong f)

end Existence

#check @DividedPowers.extendsAlong_of_map_eq_bot
#check @DividedPowers.extendsAlong_of_isPrincipal
#check @DividedPowers.extendsAlong_of_flat
