/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Hilbert
public import ReasLib.CategoryTheory.Monoidal.InvertibleTensorPower
public import Mathlib.Algebra.Polynomial.Eval.Defs

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- For a globally polynomial function `P`, a Quot-point has Hilbert polynomial `P`
with respect to `L` if and only if it has Hilbert polynomial `fun t ↦ P ((n : ℤ) * t)`
with respect to the positive tensor power `tensorPower L n`. -/
theorem hasHilbertPolynomial_tensorPower (f : X ⟶ B) [FinitePresentation f]
    {F : X.Modules} {σ : SchemeOver B} (Q : QuotPoint f F σ)
    (L : X.Modules) [isInvertibleObject L] (P : ℤ → ℤ)
    (hP : ∃ p : Polynomial ℚ, ∀ t : ℤ, p.eval (t : ℚ) = (P t : ℚ))
    (n : ℕ) (hn : 0 < n) :
    Q.HasHilbertPolynomial L P ↔
      Q.HasHilbertPolynomial (tensorPower L n) (fun t ↦ P ((n : ℤ) * t)) := sorry

/-- For a separated finitely presented morphism and a quasi-coherent module, the
Hilbert locus for an invertible module `L` and a globally polynomial function `P`
equals the Hilbert locus for `tensorPower L n` and `fun t ↦ P ((n : ℤ) * t)`
whenever `n` is positive. -/
theorem quotHilbert_tensorPower (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F : X.Modules) [F.IsQuasicoherent] (L : X.Modules) [isInvertibleObject L]
    (P : ℤ → ℤ)
    (hP : ∃ p : Polynomial ℚ, ∀ t : ℤ, p.eval (t : ℚ) = (P t : ℚ))
    (n : ℕ) (hn : 0 < n) :
    quotHilbert f F L P =
      quotHilbert f F (tensorPower L n) (fun t ↦ P ((n : ℤ) * t)) := sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
