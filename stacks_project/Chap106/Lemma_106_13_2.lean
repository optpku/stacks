/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic
public import stacks_project.Chap100.Definition_100_6_1_QuasiCompact
public import stacks_project.Chap100.Example_100_12_5_Quotient
public import stacks_project.Chap101.Definition_101_4_2_Separation
public import stacks_project.Chap106.Definition_106_13_1_WellNighAffine

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
`(ofGroupoidScheme G).quotientStack ⟶ X`. -/
def existsAffineFiniteLocallyFreeGroupoid {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] : Prop :=
  ∃ (G : GroupoidScheme S) (e : (ofGroupoidScheme G).quotientStack ⟶ X),
    IsAffine G.U.left ∧ IsAffine G.R.left ∧ IsFiniteLocallyFree G.s.left ∧
      IsFiniteLocallyFree G.t.left ∧ (toBasedFunctor e).IsEquivalence

namespace existsAffineFiniteLocallyFreeGroupoid

/-- `existsAffineFiniteLocallyFreeGroupoid X` unpacks to an affine finite
locally free groupoid scheme and an equivalence from its quotient stack. -/
theorem iff {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    existsAffineFiniteLocallyFreeGroupoid X ↔
      ∃ (G : GroupoidScheme S) (e : (ofGroupoidScheme G).quotientStack ⟶ X),
        IsAffine G.U.left ∧ IsAffine G.R.left ∧ IsFiniteLocallyFree G.s.left ∧
          IsFiniteLocallyFree G.t.left ∧ (toBasedFunctor e).IsEquivalence :=
  sorry

/-- An affine finite locally free groupoid scheme with an equivalence from its
quotient stack witnesses `existsAffineFiniteLocallyFreeGroupoid`. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (G : GroupoidScheme S) (e : (ofGroupoidScheme G).quotientStack ⟶ X)
    [IsAffine G.U.left] [IsAffine G.R.left] [IsFiniteLocallyFree G.s.left]
    [IsFiniteLocallyFree G.t.left] [(toBasedFunctor e).IsEquivalence] :
    existsAffineFiniteLocallyFreeGroupoid X :=
  sorry

/-- `existsAffineFiniteLocallyFreeGroupoid X` supplies an affine finite locally
free groupoid scheme and an equivalence from its quotient stack. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h : existsAffineFiniteLocallyFreeGroupoid X) :
    ∃ (G : GroupoidScheme S) (e : (ofGroupoidScheme G).quotientStack ⟶ X),
      IsAffine G.U.left ∧ IsAffine G.R.left ∧ IsFiniteLocallyFree G.s.left ∧
        IsFiniteLocallyFree G.t.left ∧ (toBasedFunctor e).IsEquivalence :=
  sorry

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

/-- Lemma 106.13.2 (1). Let `X` be an algebraic stack. The following are equivalent:
`X` is well-nigh affine, and there exists a groupoid scheme `(U, R, s, t, c)`
with `U` and `R` affine and `s, t : R ⟶ U` finite locally free such that `X`
is equivalent to `[U / R]`. -/
@[stacks 0DUM]
theorem isWellNighAffine_iff_existsAffineFiniteLocallyFreeGroupoid
    {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    IsWellNighAffine X ↔ existsAffineFiniteLocallyFreeGroupoid X :=
  sorry

/-- Lemma 106.13.2 (2). A well-nigh affine algebraic stack is quasi-compact. -/
@[stacks 0DUM, instance]
instance instIsQuasiCompact_of_isWellNighAffine {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] [IsWellNighAffine X] :
    IsQuasiCompact X :=
  sorry

/-- Lemma 106.13.2 (3). A well-nigh affine algebraic stack is quasi-DM. -/
@[stacks 0DUM, instance]
instance instIsQuasiDM_of_isWellNighAffine {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] [IsWellNighAffine X] :
    IsQuasiDM X :=
  sorry

/-- Lemma 106.13.2 (4). A well-nigh affine algebraic stack is separated. -/
@[stacks 0DUM, instance]
instance instIsSeparated_of_isWellNighAffine {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] [IsWellNighAffine X] :
    IsSeparated X :=
  sorry

end AlgebraicGeometry.AlgebraicStack
