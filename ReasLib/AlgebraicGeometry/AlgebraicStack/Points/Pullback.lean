/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points

/-!
# Points of a 2-fibre product of algebraic stacks

A 2-commutative square of algebraic stacks induces a comparison from points of its apex to
the set-theoretic fibre product of points. For a 2-fibre product square, this comparison is
surjective, though not in general injective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits CategoryTheory.Bicategory

open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Points

/-- The set-theoretic fibre product of points of algebraic stacks over a common target. -/
abbrev pullbackObj {S : Scheme.{u}} {X Z Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Z] [AlgebraicStack Y]
    (f : X ⟶ Y) (g : Z ⟶ Y) : Type (u + 1) :=
  Types.PullbackObj (TypeCat.ofHom (map f)) (TypeCat.ofHom (map g))

section

variable {S : Scheme.{u}} {P X Z Y : GroupoidsOver S}
variable [AlgebraicStack P] [AlgebraicStack X] [AlgebraicStack Z] [AlgebraicStack Y]
variable {fst : P ⟶ X} {snd : P ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y}

/-- The two legs of a 2-commutative square of algebraic stacks agree after mapping to points of
the common target. -/
theorem pullbackComparison_condition (iso : fst ≫ f ≅ snd ≫ g)
    (p : Points P) : map f (map fst p) = map g (map snd p) := sorry

/-- The comparison of points associated to a 2-commutative square of algebraic stacks. -/
def pullbackComparison (iso : fst ≫ f ≅ snd ≫ g) : Points P → pullbackObj f g :=
  fun p ↦ ⟨(map fst p, map snd p), pullbackComparison_condition iso p⟩

/-- The first component of the points comparison is the map on points induced by `fst`. -/
theorem pullbackComparison_fst (iso : fst ≫ f ≅ snd ≫ g)
    (p : Points P) : (pullbackComparison iso p).1.1 = map fst p := rfl

/-- The second component of the points comparison is the map on points induced by `snd`. -/
theorem pullbackComparison_snd (iso : fst ≫ f ≅ snd ≫ g)
    (p : Points P) : (pullbackComparison iso p).1.2 = map snd p := rfl

/-- The points comparison sends a point of the apex to the compatible pair of its images. -/
theorem pullbackComparison_apply (iso : fst ≫ f ≅ snd ≫ g)
    (p : Points P) :
    pullbackComparison iso p =
      ⟨(map fst p, map snd p), pullbackComparison_condition iso p⟩ := rfl

/-- The comparison of points of a 2-fibre product square of algebraic stacks is surjective. -/
theorem pullbackComparison_surjective (iso : fst ≫ f ≅ snd ≫ g)
    (h : (PseudoPullbackCone.mk f g P fst snd iso).IsBilimit) :
    Function.Surjective (pullbackComparison iso) := sorry

/-- A compatible pair of points of `X` and `Z` over `Y` lifts to a point of a 2-fibre product
apex. -/
theorem exists_of_map_eq (iso : fst ≫ f ≅ snd ≫ g)
    (h : (PseudoPullbackCone.mk f g P fst snd iso).IsBilimit)
    (x : Points X) (z : Points Z) (hxz : map f x = map g z) :
    ∃ p : Points P, map fst p = x ∧ map snd p = z := sorry

end

end AlgebraicGeometry.AlgebraicStack.Points
