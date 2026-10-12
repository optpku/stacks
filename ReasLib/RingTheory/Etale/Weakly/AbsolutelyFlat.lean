/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AbsolutelyFlat.Dimension
public import ReasLib.RingTheory.Etale.Weakly.TensorSquare
public import ReasLib.RingTheory.WeakDimension.WeaklyEtale
import Mathlib.Tactic.CrossRefAttribute

/-!
# Absolutely flat and reduced targets of weakly etale maps

This module records ascent properties of a flat tensor-square multiplication map. The first
theorem keeps the multiplication-map hypothesis explicit; the second uses the canonical
`Algebra.WeaklyEtale` owner.
-/

@[expose] public section

universe u v

namespace IsAbsolutelyFlatRing

variable (A : Type u) (B : Type v)
variable [CommRing A] [CommRing B] [Algebra A B]

/-- Over an absolutely flat ring, flatness of tensor-square multiplication makes the target
absolutely flat. -/
@[stacks 092I "Lemma 15.105.8 (1)"]
theorem of_tensorSquareMultiplication_flat [IsAbsolutelyFlatRing A]
    (hflat : (Algebra.tensorSquareMultiplication A B).Flat) :
    IsAbsolutelyFlatRing B := sorry

/-- A weakly etale algebra over an absolutely flat ring is absolutely flat. -/
@[stacks 092I "weakly etale ascent of absolute flatness"]
theorem of_weaklyEtale [IsAbsolutelyFlatRing A]
    (hAB : Algebra.WeaklyEtale A B) : IsAbsolutelyFlatRing B := sorry

end IsAbsolutelyFlatRing

namespace Algebra.WeaklyEtale

variable (A : Type u) (B : Type v)
variable [CommRing A] [CommRing B] [Algebra A B]

/-- Reducedness ascends along a weakly etale map. -/
@[stacks 092I "Lemma 15.105.8 (2)"]
theorem isReduced [IsReduced A]
    (hAB : Algebra.WeaklyEtale A B) : IsReduced B := sorry

end Algebra.WeaklyEtale
