/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsoluteTransformations.Maps
public import stacks_project.Chap100.Lemma_100_11_2_Reduced
public import stacks_project.Chap101.Definition_101_50_1_Decent
public import stacks_project.Chap107.Lemma_107_5_24_Jacobson

/-!
# Integral algebraic stacks

An algebraic stack is integral when it is reduced, decent, its inertia
morphism is quasi-compact, and its space of points is irreducible. This is
strictly stronger than reduced and irreducible.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids (inertia)
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The inertia stack of an algebraic stack is an algebraic stack. -/
instance instAlgebraicStack_inertia {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] : AlgebraicStack (inertia.{u + 1, u, u, u + 1} X) :=
  sorry

/-- An algebraic stack is integral if it is reduced, decent, the inertia
morphism `I_X ⟶ X` is quasi-compact, and `|X|` is irreducible. -/
@[mk_iff]
class IsIntegral {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    Prop extends IsReduced X, IsDecent X, IsIrreducible X where
  /-- The inertia morphism `I_X ⟶ X` is quasi-compact. -/
  inertia_quasiCompact : QuasiCompact (forget.{u + 1, u, u, u + 1} X)

namespace IsIntegral

/-- An integral algebraic stack is reduced and decent, has quasi-compact
inertia morphism, and is irreducible. -/
theorem spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsIntegral X] :
    IsReduced X ∧ IsDecent X ∧ QuasiCompact (forget.{u + 1, u, u, u + 1} X) ∧
      IsIrreducible X :=
  sorry

/-- Reducedness, decency, quasi-compact inertia, and irreducibility together
witness that an algebraic stack is integral. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [IsReduced X] [IsDecent X] [IsIrreducible X]
    [QuasiCompact (forget.{u + 1, u, u, u + 1} X)] : IsIntegral X :=
  sorry

end IsIntegral

/-- The canonical slice of an integral scheme over `S` is an integral algebraic
stack. -/
instance instIsIntegral_slice {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsIntegral U.left] :
    IsIntegral (GroupoidsOver.slice U) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
