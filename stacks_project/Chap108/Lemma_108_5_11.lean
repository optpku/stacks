/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap108.Lemma_108_5_10_Hilbert
public import stacks_project.Chap69.Lemma_69_20_1_Tensor

/-!
# Lemma 108.5.11

The Hilbert-polynomial loci `Quot^{P, L}_{F/X/B}` and
`Quot^{P', L^{⊗ n}}_{F/X/B}` of the Grothendieck Quot functor coincide when
`P'(t) = P(n t)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Integral tensor powers of an invertible `𝒪_X`-module remain invertible. -/
instance instIsInvertibleObject_tensorPowerInt (L : X.Modules)
    [isInvertibleObject L] (n : ℕ) :
    isInvertibleObject (tensorPowerInt L n) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace.Quot

/-- A Quot-point has Hilbert polynomial `P` with respect to `L` if and only if it
has Hilbert polynomial `t ↦ P(n t)` with respect to `L^{⊗ n}`. -/
theorem hasHilbertPolynomial_tensorPower (f : X ⟶ B) [FinitePresentation f]
    {F : X.Modules} {σ : SchemesOver B} (Q : QuotPoint f F σ)
    (L : X.Modules) [isInvertibleObject L] (P : ℤ → ℤ)
    (hP : IsNumericalPolynomial P) (n : ℕ) (hn : 0 < n) :
    Q.HasHilbertPolynomial L P ↔
      Q.HasHilbertPolynomial (tensorPowerInt L n) (fun t ↦ P ((n : ℤ) * t)) :=
  sorry

/-- Lemma 108.5.11: let `f : X ⟶ B` be separated and of finite presentation and
let `F` be a quasi-coherent `𝒪_X`-module. Let `L` be an invertible `𝒪_X`-module,
let `P : ℤ → ℤ` be a numerical polynomial, and let `n` be a positive integer.
Then the Hilbert-polynomial open-and-closed loci satisfy
`Quot^{P, L}_{F/X/B} = Quot^{P', L^{⊗ n}}_{F/X/B}`, where `P'(t) = P(n t)`. -/
@[stacks 0DP8]
theorem quotHilbert_tensorPower (f : X ⟶ B) [FinitePresentation f] [Separated f]
    (F : X.Modules) [F.IsQuasicoherent] (L : X.Modules) [isInvertibleObject L]
    (P : ℤ → ℤ) (hP : IsNumericalPolynomial P) (n : ℕ) (hn : 0 < n) :
    quotHilbert f F L P =
      quotHilbert f F (tensorPowerInt L n) (fun t ↦ P ((n : ℤ) * t)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
