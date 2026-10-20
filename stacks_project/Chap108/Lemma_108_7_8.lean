module

public import stacks_project.Chap71.Definition_71_18_1_StrictTransform
public import stacks_project.Chap108.Lemma_108_6_4

/-!
# Lemma 108.7.8

The Hilbert-polynomial algebraic space of closed subschemes, taken with
respect to a relatively ample invertible module, is separated of finite
presentation over the base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.MonoidalCategory.InvertiblePower

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hilbert

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
  [FinitePresentation f] [Separated f] (L : X.Modules) [isInvertibleObject L]
  [AlgebraicGeometry.AlgebraicSpace.RelativelyAmple f L] (P : ℤ → ℤ)

/-- Lemma 108.7.8 (1): if `f : X ⟶ B` is a separated morphism of finite
presentation of algebraic spaces and `L` is an invertible `𝒪_X`-module ample
on `X/B` in the sense of Definition 71.14.1, then the algebraic space
`Hilb^P_{X/B}` parametrizing closed subschemes with Hilbert polynomial `P`
with respect to `L` is separated over `B`. Here `Hilb^P_{X/B}` is the
Hilbert-polynomial locus `quotHilbert` of `𝒪_X`. -/
@[stacks 0DPI]
instance instIsSeparatedOver_hilbertPolynomial :
    Quot.IsSeparatedOver
      (Quot.quotHilbert f (SheafOfModules.unit (structureSheaf X)) L P).toFunctor :=
  sorry

/-- Lemma 108.7.8 (2): if `f : X ⟶ B` is a separated morphism of finite
presentation of algebraic spaces and `L` is an invertible `𝒪_X`-module ample
on `X/B` in the sense of Definition 71.14.1, then the algebraic space
`Hilb^P_{X/B}` parametrizing closed subschemes with Hilbert polynomial `P`
with respect to `L` is of finite presentation over `B`. Here `Hilb^P_{X/B}`
is the Hilbert-polynomial locus `quotHilbert` of `𝒪_X`. -/
@[stacks 0DPI]
theorem hilbertPolynomial_isFinitePresentationOver :
    IsFinitePresentationOver
      (Quot.quotHilbert f (SheafOfModules.unit (structureSheaf X)) L P).toFunctor :=
  sorry

/-- Finite presentation of the Hilbert-polynomial functor over `B` means some
representing morphism of algebraic spaces over `B` is of finite presentation. -/
theorem hilbertPolynomial_isFinitePresentationOver_spec :
    IsFinitePresentationOver
        (Quot.quotHilbert f (SheafOfModules.unit (structureSheaf X)) L P).toFunctor ↔
      ∃ (Q : AlgebraicSpace S) (π : Q ⟶ B),
        FinitePresentation π ∧
          Nonempty
            ((Quot.quotHilbert f (SheafOfModules.unit (structureSheaf X)) L P).toFunctor ≅
              yonedaOver π) :=
  sorry

/-- The Hilbert-polynomial locus is represented by a morphism of algebraic
spaces over `B` that is both separated and of finite presentation. -/
theorem hilbertPolynomial_exists_separated_finitePresentation :
    ∃ (Q : AlgebraicSpace S) (π : Q ⟶ B),
      Separated π ∧ FinitePresentation π ∧
        Nonempty
          ((Quot.quotHilbert f (SheafOfModules.unit (structureSheaf X)) L P).toFunctor ≅
            yonedaOver π) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hilbert
