module

public import stacks_project.Chap101.Definition_101_50_1_Decent
public import stacks_project.Chap101.Definition_101_50_1_Integral
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

universe u

/- Definition 101.50.1: an algebraic stack `X` is integral if it is reduced,
decent, `I_X ⟶ X` is quasi-compact, and `|X|` is irreducible. -/
@[stacks 0GWB] #check (isIntegral_iff :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    IsIntegral X ↔
      IsReduced X ∧ IsDecent X ∧ IsIrreducible X ∧
        QuasiCompact (forget.{u + 1, u, u, u + 1} X))
