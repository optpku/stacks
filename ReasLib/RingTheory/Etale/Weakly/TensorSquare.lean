/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Etale.Weakly
public import ReasLib.RingTheory.Algebra.TensorProduct.Multiplication
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor-square criteria for weakly etale algebras

The map-level tensor-square multiplication is the canonical owner of the diagonal
condition.  This leaf provides the small bridge to Mathlib's `WeaklyEtale` class;
the source-facing field specialization lives in `Weakly.Field`.
@stack 092B
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Algebra.WeaklyEtale

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- A flat tensor-square multiplication map, together with base flatness, is a weakly etale
algebra. -/
@[stacks 092B "weakly etale from tensor-square flatness"]
theorem of_tensorSquareMul_flat [Module.Flat R S]
    (hflat : (Algebra.tensorSquareMultiplication R S).Flat) :
    Algebra.WeaklyEtale R S := by
  refine { flat_lmul' := ?_ }
  simpa only [Algebra.tensorSquareMultiplication] using hflat

/-- Under the ambient module-flatness hypothesis, weakly etaleness is equivalent to flatness of
the canonical tensor-square multiplication map. -/
@[stacks 092B "weakly etale tensor-square criterion"]
theorem iff_tensorSquareMul_flat [Module.Flat R S] :
    Algebra.WeaklyEtale R S ↔
      (Algebra.tensorSquareMultiplication R S).Flat := by
  exact ⟨tensorSquare_flat, of_tensorSquareMul_flat⟩

end Algebra.WeaklyEtale
