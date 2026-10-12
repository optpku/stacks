/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap108.Lemma_108_6_4
public import stacks_project.Chap108.Remark_108_10_4_Numerical_invariants_Locus
public import stacks_project.Chap108.Lemma_108_10_5_ExternalTensor

/-!
# Lemma 108.10.5

The numerical relative-Hom functor `Mor^{P, M}_B(Y, X)` is separated and of
finite presentation over `B`, where `M` is the external tensor product of
relatively ample invertible modules on `Y / B` and `X / B`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

variable {S : Scheme.{u}} {Y B X : AlgebraicSpace S}

/-- Lemma 108.10.5 (1): with `B`, `X`, `Y` as in the introduction of this
section, if `L` is ample on `X / B` and `N` is ample on `Y / B` in the sense of
`RelativelyAmple`, and `P : ℤ → ℤ` is a numerical polynomial, then
`morNumericalHilbert y x M P` is separated over `B`, where
`M = externalTensorProduct y x N L` is `pr₁^* N ⊗ pr₂^* L` on `Y ×_B X`. -/
@[stacks 0DPR]
instance instIsSeparatedOver_morNumericalHilbert (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y] [Separated x] [FinitePresentation x]
    (N : Y.Modules) (L : X.Modules) [isInvertibleObject N] [isInvertibleObject L]
    [AlgebraicGeometry.AlgebraicSpace.RelativelyAmple y N]
    [AlgebraicGeometry.AlgebraicSpace.RelativelyAmple x L] (P : ℤ → ℤ) :
    Quot.IsSeparatedOver
      (morNumericalHilbert y x (Modules.externalTensorProduct y x N L) P).toFunctor :=
  sorry

/-- Lemma 108.10.5 (2): with `B`, `X`, `Y` as in the introduction of this
section, if `L` is ample on `X / B` and `N` is ample on `Y / B` in the sense of
`RelativelyAmple`, and `P : ℤ → ℤ` is a numerical polynomial, then
`morNumericalHilbert y x M P` is of finite presentation over `B`, where
`M = externalTensorProduct y x N L` is `pr₁^* N ⊗ pr₂^* L` on `Y ×_B X`. -/
@[stacks 0DPR]
theorem isFinitePresentationOver_morNumericalHilbert (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y] [Separated x] [FinitePresentation x]
    (N : Y.Modules) (L : X.Modules) [isInvertibleObject N] [isInvertibleObject L]
    [AlgebraicGeometry.AlgebraicSpace.RelativelyAmple y N]
    [AlgebraicGeometry.AlgebraicSpace.RelativelyAmple x L] (P : ℤ → ℤ) :
    IsFinitePresentationOver
      (morNumericalHilbert y x (Modules.externalTensorProduct y x N L) P).toFunctor :=
  sorry

/-- Finite presentation of `morNumericalHilbert y x (externalTensorProduct y x N L) P`
over `B` means some representing morphism of algebraic spaces over `B` is of
finite presentation. -/
theorem isFinitePresentationOver_morNumericalHilbert_spec (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y] [Separated x] [FinitePresentation x]
    (N : Y.Modules) (L : X.Modules) [isInvertibleObject N] [isInvertibleObject L]
    [AlgebraicGeometry.AlgebraicSpace.RelativelyAmple y N]
    [AlgebraicGeometry.AlgebraicSpace.RelativelyAmple x L] (P : ℤ → ℤ) :
    IsFinitePresentationOver
        (morNumericalHilbert y x (Modules.externalTensorProduct y x N L) P).toFunctor ↔
      ∃ (Q : AlgebraicSpace S) (π : Q ⟶ B),
        FinitePresentation π ∧
          Nonempty
            ((morNumericalHilbert y x (Modules.externalTensorProduct y x N L) P).toFunctor ≅
              yonedaOver π) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
