/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.StandardSmooth
public import ReasLib.RingTheory.RingHom.IndSmooth.Basic

/-!
# Ind-standard-smooth ring maps

This leaf defines filtered colimits of standard-smooth maps using the same
common-universe ring-hom lift as ind-smoothness.
-/

@[expose] public section

open CategoryTheory MorphismProperty

universe u v

namespace RingHom

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/-- A ring homomorphism is ind-standard-smooth if its common-universe lift is
a filtered colimit of standard-smooth morphisms. -/
@[stacks 07CI]
abbrev IndStandardSmooth (f : R →+* A) : Prop :=
  CategoryTheory.MorphismProperty.ind.{max u v, max u v, max u v + 1}
    (toMorphismProperty IsStandardSmooth) (CommRingCat.ofHom f.ulift.{v, u})

namespace IndSmooth

/-- Every ind-smooth ring homomorphism is ind-standard-smooth. -/
@[stacks 07CI]
theorem indStandardSmooth {f : R →+* A}
    (h : f.IndSmooth) :
    f.IndStandardSmooth := sorry

end IndSmooth

end RingHom
