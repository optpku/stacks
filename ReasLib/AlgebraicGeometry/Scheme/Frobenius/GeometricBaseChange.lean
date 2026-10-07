module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Geometric

/-!
# Absolute Frobenius and base change of geometric Frobenius
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Scheme
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- For a finite field `k` with `p ^ f` elements, the `f`-fold absolute Frobenius
on the algebraic-closure base change of `Spec k` differs from the base change of
the geometric Frobenius of `Spec k` over `k`. -/
theorem baseChange_ne_absoluteFrobeniusPow [Fintype k]
    (p : ℕ) [Fact p.Prime] [CharP k p] (f : ℕ)
    (hcard : Fintype.card k = p ^ f) [Algebra k (AlgebraicClosure k)] :
    geometricFrobenius p f (FieldExtension.Over.baseChange k (AlgebraicClosure k)
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))) ≠
      ((FieldExtension.Over.functor k (AlgebraicClosure k)).map
        (geometricFrobeniusOver p f hcard (Over.mk (𝟙 (Spec (CommRingCat.of k)))))).left := sorry

end AlgebraicGeometry.SchemeOverField
