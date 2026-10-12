/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Ring.Subring.Basic
public import ReasLib.RingTheory.Algebra.TensorProduct.RingHom

@[expose] public section

universe u v

namespace Algebra.TensorProduct.RingHom

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- The two maps from the equalizer of a pair of ring homomorphisms agree after
composition with the respective homomorphisms. -/
theorem eqLocusSquare_comm (right left : A →+* B) :
    left.comp (right.eqLocus left).subtype =
      right.comp (right.eqLocus left).subtype := sorry

/-- The commutative square formed by the equalizer inclusion and a pair of ring
homomorphisms. -/
def eqLocusSquare (right left : A →+* B) :
    Square (X := right.eqLocus left) (Y := A) (Z := A) (W := B) where
  sourceLeft := (right.eqLocus left).subtype
  sourceRight := (right.eqLocus left).subtype
  leftTarget := left
  rightTarget := right
  comm := eqLocusSquare_comm right left

end Algebra.TensorProduct.RingHom
