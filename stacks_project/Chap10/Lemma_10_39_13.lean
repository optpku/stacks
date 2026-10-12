/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.ShortComplex.UniversallyExact.Flat
import StacksCheckRecall

/-!
# Lemma 10.39.13
@stack 00HM
-/

@[expose] public section

universe u v

namespace CategoryTheory.ShortComplex

variable {R : Type u} [CommRing R]

section middle

variable {S : ShortComplex (ModuleCat.{v} R)}
variable [Module.Flat R S.X₁] [Module.Flat R S.X₃]

/- Lemma 10.39.13 (1): in a short exact sequence, flatness of the left
and right terms implies flatness of the middle term. -/
@[stacks 00HM "(1)"]
#check (ShortExact.flat_X₂ (S := S) :
  S.ShortExact → Module.Flat R S.X₂)

end middle

section left

variable {S : ShortComplex (ModuleCat.{v} R)}
variable [Module.Flat R S.X₂] [Module.Flat R S.X₃]

/- Lemma 10.39.13 (2): in a short exact sequence, flatness of the middle
and right terms implies flatness of the left term. -/
@[stacks 00HM "(2)"]
#check (ShortExact.flat_X₁ (S := S) :
  S.ShortExact → Module.Flat R S.X₁)

end left

end CategoryTheory.ShortComplex
