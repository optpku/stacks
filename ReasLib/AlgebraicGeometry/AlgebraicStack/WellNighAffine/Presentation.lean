/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.WellNighAffine
public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Object
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.OfScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Small
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic

/-!
# Well-nigh affine algebraic stacks via affine finite locally free groupoids

An algebraic stack is well-nigh affine if and only if it is equivalent to the
quotient stack of a groupoid scheme with affine object and arrow schemes and
finite locally free source and target. Such a stack is quasi-compact, quasi-DM,
and separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry GroupoidAlgebraicSpace
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- There exists a groupoid scheme `(U, R, s, t, c)` over `S` with `U` and `R`
affine and `s, t : R ⟶ U` finite locally free, together with an equivalence
from its canonical quotient stack to `X`. -/
def existsAffineFiniteLocallyFreeGroupoid {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] : Prop :=
  ∃ (G : GroupoidScheme S) (e : GroupoidAlgebraicSpace.SmallQuotient.quotientStack
      (GroupoidAlgebraicSpace.ofScheme G) ⟶ X),
    IsAffine G.U.left ∧ IsAffine G.R.left ∧ IsFiniteLocallyFree G.s.left ∧
      IsFiniteLocallyFree G.t.left ∧ (toBasedFunctor e).IsEquivalence

namespace existsAffineFiniteLocallyFreeGroupoid

/-- `existsAffineFiniteLocallyFreeGroupoid X` unpacks to an affine finite
locally free groupoid scheme and an equivalence from its quotient stack. -/
theorem iff {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    existsAffineFiniteLocallyFreeGroupoid X ↔
      ∃ (G : GroupoidScheme S) (e : GroupoidAlgebraicSpace.SmallQuotient.quotientStack
      (GroupoidAlgebraicSpace.ofScheme G) ⟶ X),
        IsAffine G.U.left ∧ IsAffine G.R.left ∧ IsFiniteLocallyFree G.s.left ∧
          IsFiniteLocallyFree G.t.left ∧ (toBasedFunctor e).IsEquivalence :=
  Iff.rfl

/-- An affine finite locally free groupoid scheme with an equivalence from its
quotient stack witnesses `existsAffineFiniteLocallyFreeGroupoid`. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (G : GroupoidScheme S) (e : GroupoidAlgebraicSpace.SmallQuotient.quotientStack
      (GroupoidAlgebraicSpace.ofScheme G) ⟶ X)
    [IsAffine G.U.left] [IsAffine G.R.left] [IsFiniteLocallyFree G.s.left]
    [IsFiniteLocallyFree G.t.left] [(toBasedFunctor e).IsEquivalence] :
    existsAffineFiniteLocallyFreeGroupoid X :=
  ⟨G, e, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- `existsAffineFiniteLocallyFreeGroupoid X` supplies an affine finite locally
free groupoid scheme and an equivalence from its quotient stack. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h : existsAffineFiniteLocallyFreeGroupoid X) :
    ∃ (G : GroupoidScheme S) (e : GroupoidAlgebraicSpace.SmallQuotient.quotientStack
      (GroupoidAlgebraicSpace.ofScheme G) ⟶ X),
      IsAffine G.U.left ∧ IsAffine G.R.left ∧ IsFiniteLocallyFree G.s.left ∧
        IsFiniteLocallyFree G.t.left ∧ (toBasedFunctor e).IsEquivalence :=
  h

/-- An algebraic stack equivalent to `[U / R]` for an affine finite locally free
groupoid scheme is well-nigh affine. -/
theorem isWellNighAffine {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (h : existsAffineFiniteLocallyFreeGroupoid X) :
    IsWellNighAffine X :=
  sorry

end existsAffineFiniteLocallyFreeGroupoid

namespace IsWellNighAffine

/-- A well-nigh affine algebraic stack admits an affine finite locally free
groupoid presentation. -/
theorem existsAffineFiniteLocallyFreeGroupoid {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] [IsWellNighAffine X] :
    existsAffineFiniteLocallyFreeGroupoid X :=
  sorry

end IsWellNighAffine

/-- An algebraic stack admits the following equivalent descriptions:
`X` is well-nigh affine, and there exists a groupoid scheme `(U, R, s, t, c)`
with `U` and `R` affine and `s, t : R ⟶ U` finite locally free such that `X`
is equivalent to `[U / R]`. -/
theorem isWellNighAffine_iff_existsAffineFiniteLocallyFreeGroupoid
    {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    IsWellNighAffine X ↔ existsAffineFiniteLocallyFreeGroupoid X :=
  ⟨fun _ => IsWellNighAffine.existsAffineFiniteLocallyFreeGroupoid X,
    existsAffineFiniteLocallyFreeGroupoid.isWellNighAffine⟩

/-- A well-nigh affine algebraic stack is quasi-compact. -/
instance instIsQuasiCompact_of_isWellNighAffine {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] [IsWellNighAffine X] :
    IsQuasiCompact X :=
  sorry

/-- A well-nigh affine algebraic stack is quasi-DM. -/
instance instIsQuasiDM_of_isWellNighAffine {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] [IsWellNighAffine X] :
    IsQuasiDM X :=
  sorry

/-- A well-nigh affine algebraic stack is separated. -/
instance instIsSeparated_of_isWellNighAffine {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] [IsWellNighAffine X] :
    IsSeparated X :=
  sorry

end AlgebraicGeometry.AlgebraicStack
