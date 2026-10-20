/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.WellNighAffine.Presentation
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

/- Lemma 106.13.2. Let `X` be an algebraic stack. The following are equivalent:
`X` is well-nigh affine, and there exists a groupoid scheme `(U, R, s, t, c)`
with `U` and `R` affine and `s, t : R ⟶ U` finite locally free such that
`X` is equivalent to `[U / R]`. If these conditions hold, then `X` is
quasi-compact, quasi-DM, and separated. -/
@[stacks 0DUM] #check
  (AlgebraicGeometry.AlgebraicStack.isWellNighAffine_iff_existsAffineFiniteLocallyFreeGroupoid :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
      IsWellNighAffine X ↔ existsAffineFiniteLocallyFreeGroupoid X)

#check (AlgebraicGeometry.AlgebraicStack.existsAffineFiniteLocallyFreeGroupoid :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], Prop)

#check (AlgebraicGeometry.AlgebraicStack.existsAffineFiniteLocallyFreeGroupoid.iff :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
      existsAffineFiniteLocallyFreeGroupoid X ↔
        ∃ (G : GroupoidScheme S)
          (e : GroupoidAlgebraicSpace.SmallQuotient.quotientStack
            (GroupoidAlgebraicSpace.ofScheme G) ⟶ X),
          IsAffine G.U.left ∧ IsAffine G.R.left ∧ IsFiniteLocallyFree G.s.left ∧
            IsFiniteLocallyFree G.t.left ∧ (toBasedFunctor e).IsEquivalence)

#check (AlgebraicGeometry.AlgebraicStack.existsAffineFiniteLocallyFreeGroupoid.of :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
      (G : GroupoidScheme S)
      (e : GroupoidAlgebraicSpace.SmallQuotient.quotientStack
        (GroupoidAlgebraicSpace.ofScheme G) ⟶ X)
      [IsAffine G.U.left] [IsAffine G.R.left] [IsFiniteLocallyFree G.s.left]
      [IsFiniteLocallyFree G.t.left] [(toBasedFunctor e).IsEquivalence],
      existsAffineFiniteLocallyFreeGroupoid X)

#check (AlgebraicGeometry.AlgebraicStack.existsAffineFiniteLocallyFreeGroupoid.spec :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
      existsAffineFiniteLocallyFreeGroupoid X →
        ∃ (G : GroupoidScheme S)
          (e : GroupoidAlgebraicSpace.SmallQuotient.quotientStack
            (GroupoidAlgebraicSpace.ofScheme G) ⟶ X),
          IsAffine G.U.left ∧ IsAffine G.R.left ∧ IsFiniteLocallyFree G.s.left ∧
            IsFiniteLocallyFree G.t.left ∧ (toBasedFunctor e).IsEquivalence)

#check (AlgebraicGeometry.AlgebraicStack.existsAffineFiniteLocallyFreeGroupoid.isWellNighAffine :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
      existsAffineFiniteLocallyFreeGroupoid X → IsWellNighAffine X)

#check (AlgebraicGeometry.AlgebraicStack.IsWellNighAffine.existsAffineFiniteLocallyFreeGroupoid :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] [IsWellNighAffine X],
      existsAffineFiniteLocallyFreeGroupoid X)

#check (AlgebraicGeometry.AlgebraicStack.instIsQuasiCompact_of_isWellNighAffine :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] [IsWellNighAffine X],
      IsQuasiCompact X)

#check (AlgebraicGeometry.AlgebraicStack.instIsQuasiDM_of_isWellNighAffine :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] [IsWellNighAffine X],
      IsQuasiDM X)

#check (AlgebraicGeometry.AlgebraicStack.instIsSeparated_of_isWellNighAffine :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] [IsWellNighAffine X],
      IsSeparated X)
