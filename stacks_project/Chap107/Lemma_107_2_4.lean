module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.VersalRing.Existence
import StacksCheckRecall

/-!
# Existence and uniqueness of versal rings at finite-type points

In Situation 107.2.1, a finite-type field-valued point of an algebraic stack
admits a versal ring, unique up to an `S`-algebra power-series extension in one
direction or the other.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 107.2.4 (1): In Situation 107.2.1 let `x0 : Spec(k) ⟶ X` be a morphism,
where `k` is a finite type field over `S`. Then a versal ring to `X` at `x0`
exists. -/
@[stacks 0DQX] #check (AlgebraicGeometry.AlgebraicStack.exists_isVersalRing :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom],
    ∃ A : CompleteLocalSAlgebra S, IsVersalRing x0 A)

/- Lemma 107.2.4 (2): In Situation 107.2.1, given a pair `A`, `A'` of versal
rings to `X` at a finite type field-valued point `x0 : Spec(k) ⟶ X`, one has
`A ≅ A'[[t₁, …, tᵣ]]` or `A' ≅ A[[t₁, …, tᵣ]]` as `S`-algebras for some `r`. -/
@[stacks 0DQX] #check (AlgebraicGeometry.AlgebraicStack.exists_isPowerSeriesExtension_or :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A A' : CompleteLocalSAlgebra S) [IsVersalRing x0 A] [IsVersalRing x0 A'],
    (∃ φ : CompleteLocalSAlgebra.Hom A A', IsPowerSeriesExtension φ) ∨
      ∃ φ : CompleteLocalSAlgebra.Hom A' A, IsPowerSeriesExtension φ)

end AlgebraicGeometry.AlgebraicStack
