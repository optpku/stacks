/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.«101_39_1_1_ValuativeSquare»

/-!
# Valuative squares of algebraic stacks with factored generic arrows

This module packages 2-commutative valuative squares whose generic 1-morphism
factors through a fixed morphism of algebraic stacks.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A valuative 2-commutative square for `f` whose generic 1-morphism factors
through `h`. -/
structure ValuativeCommSqFactorsThrough {S : Scheme.{u}} {U X Y : GroupoidsOver S}
    [AlgebraicStack U] [AlgebraicStack X] [AlgebraicStack Y]
    (h : U ⟶ X) (f : X ⟶ Y) where
  /-- The underlying valuative 2-commutative square over `f`. -/
  sq : ValuativeCommSq f
  /-- A chosen factorization of the generic 1-morphism through `h`. -/
  genericToSource : GroupoidsOver.slice sq.specK ⟶ U
  /-- The chosen generic factorization composes to the generic 1-morphism of `sq`. -/
  fac : genericToSource ≫ h = sq.i₁

namespace ValuativeCommSqFactorsThrough

/-- Equip a valuative 2-commutative square with a chosen factorization of its
generic 1-morphism through `h`. -/
def of {S : Scheme.{u}} {U X Y : GroupoidsOver S}
    [AlgebraicStack U] [AlgebraicStack X] [AlgebraicStack Y]
    {h : U ⟶ X} {f : X ⟶ Y} (sq : ValuativeCommSq f)
    (genericToSource : GroupoidsOver.slice sq.specK ⟶ U)
    (fac : genericToSource ≫ h = sq.i₁) : ValuativeCommSqFactorsThrough h f where
  sq := sq
  genericToSource := genericToSource
  fac := fac

/-- The solid 2-commutative cospan cone of a factored valuative square. -/
abbrev toCone {S : Scheme.{u}} {U X Y : GroupoidsOver S}
    [AlgebraicStack U] [AlgebraicStack X] [AlgebraicStack Y]
    {h : U ⟶ X} {f : X ⟶ Y} (sq : ValuativeCommSqFactorsThrough h f) :=
  sq.sq.toCone

/-- The packaged square of `ValuativeCommSqFactorsThrough.of` is the given
valuative square. -/
theorem of_sq {S : Scheme.{u}} {U X Y : GroupoidsOver S}
    [AlgebraicStack U] [AlgebraicStack X] [AlgebraicStack Y]
    {h : U ⟶ X} {f : X ⟶ Y} (sq : ValuativeCommSq f)
    (genericToSource : GroupoidsOver.slice sq.specK ⟶ U)
    (fac : genericToSource ≫ h = sq.i₁) : (of sq genericToSource fac).sq = sq :=
  sorry

/-- The generic factorization of `ValuativeCommSqFactorsThrough.of` is the given
morphism `Spec(K) ⟶ U`. -/
theorem of_genericToSource {S : Scheme.{u}} {U X Y : GroupoidsOver S}
    [AlgebraicStack U] [AlgebraicStack X] [AlgebraicStack Y]
    {h : U ⟶ X} {f : X ⟶ Y} (sq : ValuativeCommSq f)
    (genericToSource : GroupoidsOver.slice sq.specK ⟶ U)
    (fac : genericToSource ≫ h = sq.i₁) :
    (of sq genericToSource fac).genericToSource = genericToSource :=
  sorry

/-- The generic factorization of `ValuativeCommSqFactorsThrough.of` composes to
the generic 1-morphism of the given valuative square. -/
theorem of_fac {S : Scheme.{u}} {U X Y : GroupoidsOver S}
    [AlgebraicStack U] [AlgebraicStack X] [AlgebraicStack Y]
    {h : U ⟶ X} {f : X ⟶ Y} (sq : ValuativeCommSq f)
    (genericToSource : GroupoidsOver.slice sq.specK ⟶ U)
    (fac : genericToSource ≫ h = sq.i₁) :
    (of sq genericToSource fac).genericToSource ≫ h = sq.i₁ :=
  sorry

/-- The generic 1-morphism of a factored valuative square is the composition
`Spec(K) ⟶ U ⟶ X`. -/
theorem spec {S : Scheme.{u}} {U X Y : GroupoidsOver S}
    [AlgebraicStack U] [AlgebraicStack X] [AlgebraicStack Y]
    {h : U ⟶ X} {f : X ⟶ Y} (sq : ValuativeCommSqFactorsThrough h f) :
    sq.genericToSource ≫ h = sq.sq.i₁ :=
  sorry

/-- The solid 2-commutative cospan cone of a factored valuative square is the
cone of the packaged valuative square. -/
theorem toCone_eq {S : Scheme.{u}} {U X Y : GroupoidsOver S}
    [AlgebraicStack U] [AlgebraicStack X] [AlgebraicStack Y]
    {h : U ⟶ X} {f : X ⟶ Y} (sq : ValuativeCommSqFactorsThrough h f) :
    sq.toCone = sq.sq.toCone :=
  sorry

end ValuativeCommSqFactorsThrough

end AlgebraicGeometry.AlgebraicStack
