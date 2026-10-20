module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Hilbert
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Rational-polynomial Hilbert loci in Quot functors

The rational Hilbert condition compares fibrewise Euler characteristics with
the values of a rational polynomial at all integer twists.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- A Quot-point has rational Hilbert polynomial `P` when every twisted fibre
has Euler characteristic equal to the corresponding rational polynomial value. -/
def QuotPoint.HasRationalHilbertPolynomial {f : X ⟶ B} [FinitePresentation f]
    {F : X.Modules} {σ : SchemeOver B} (Q : QuotPoint f F σ) (L : X.Modules)
    [isInvertibleObject L] (P : Polynomial ℚ) : Prop :=
  ∀ (k : ℤ) (t : FieldValuedPoint ((ofOverFunctor S).obj σ.left)),
    (Q.twistEulerChar L k t : ℚ) = P.eval (k : ℚ)

/-- The rational Hilbert locus consists of kernel-identified quotient classes
admitting a representative with rational Hilbert polynomial `P`. -/
def quotRationalHilbert (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L] (P : Polynomial ℚ) :
    Subfunctor (quot f F) where
  obj σ :=
    setOf fun q ↦
      ∃ Q : QuotPoint f F σ.unop,
        _root_.Quotient.mk (quotSetoid f F σ.unop) Q = q ∧
          Q.HasRationalHilbertPolynomial L P
  map := sorry

/-- Membership in the rational Hilbert locus is equivalent to admitting a
representative with the prescribed rational Hilbert polynomial. -/
theorem mem_quotRationalHilbert (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L] (P : Polynomial ℚ)
    {σ : (SchemeOver B)ᵒᵖ} (q : (quot f F).obj σ) :
    q ∈ (quotRationalHilbert f F L P).obj σ ↔
      ∃ Q : QuotPoint f F σ.unop,
        _root_.Quotient.mk (quotSetoid f F σ.unop) Q = q ∧
          Q.HasRationalHilbertPolynomial L P := sorry

/-- Rational and integer-function Hilbert loci agree whenever the integer
function agrees with rational polynomial evaluation at every integer. -/
theorem quotRationalHilbert_eq_quotHilbert (f : X ⟶ B) [FinitePresentation f]
    [Separated f] (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L]
    (P : Polynomial ℚ) (g : ℤ → ℤ) (hg : ∀ k : ℤ, (g k : ℚ) = P.eval (k : ℚ)) :
    quotRationalHilbert f F L P = quotHilbert f F L g := sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
