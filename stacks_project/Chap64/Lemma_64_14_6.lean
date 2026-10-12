/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.EtaleTrace
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicCycle AlgebraicGeometry.RelativePicard
open AlgebraicGeometry.AbelianVariety AlgebraicGeometry.Curve
open scoped AlgebraicGeometry CategoryTheory.MonObj

universe u

/- Lemma 64.14.6: in the situation of Theorem 64.14.4, the alternating trace
on constant `ZMod (ℓ ^ n)`-coefficient étale cohomology equals the fixed-point
number modulo `ℓ ^ n`. -/
@[stacks 03U3]
#check (AlgebraicGeometry.Curve.weilTraceFormula_etale :
  ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (C : SchemeOverField k) [Curve C] [Smooth C.hom] [Projective C.hom]
    (φ : C ⟶ C) (hφ : φ ≠ 𝟙 C) (ℓ n : ℕ) [Fact ℓ.Prime]
    (hℓ : IsUnit (ℓ : k)),
    etaleLefschetzNumber φ (ℓ ^ n) =
      (fixedPointNumber φ hφ : ZMod (ℓ ^ n)))
