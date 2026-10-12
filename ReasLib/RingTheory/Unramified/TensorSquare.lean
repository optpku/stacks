/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Unramified.Basic
public import ReasLib.RingTheory.Algebra.TensorProduct.Multiplication
public import ReasLib.RingTheory.RingHom.Flat.Surjective
import Mathlib.Tactic.CrossRefAttribute

/-!
# Formal unramifiedness from a flat diagonal

The tensor-square multiplication criterion is a reusable owner-level result.  It is
stated against the map-level `Algebra.tensorSquareMultiplication`, so downstream
arguments do not need to reconstruct the algebra structure induced by that map.

@stack 092M
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Algebra.FormallyUnramified

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- Stacks 092M: flatness of the diagonal multiplication map forces formal
unramifiedness of the algebra. -/
@[stacks 092M "flat tensor-square multiplication implies formal unramifiedness"]
theorem of_tensorSquareMul_flat
    (hflat : (Algebra.tensorSquareMultiplication A B).Flat) :
    Algebra.FormallyUnramified A B := by
  have hI := RingHom.Flat.ker_pure_of_surjective hflat
    Algebra.tensorSquareMultiplication.surjective
  change (KaehlerDifferential.ideal A B).Pure at hI
  letI : (KaehlerDifferential.ideal A B).Pure := hI
  exact ⟨(Ideal.cotangent_subsingleton_iff _).mpr
    (Ideal.isIdempotentElem_of_pure _)⟩

end Algebra.FormallyUnramified
