/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points

/-!
# Points of a cartesian square of algebraic spaces

A cartesian square of algebraic spaces over a scheme `S` induces a comparison from the
points of the apex to the set-theoretic fibre product of points. That comparison is
surjective, though not in general injective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Points

/-- The set-theoretic fibre product of points of algebraic spaces over a common target. -/
abbrev pullbackObj {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Type (u + 1) :=
  Types.PullbackObj (TypeCat.ofHom (map f)) (TypeCat.ofHom (map g))

section

variable {S : Scheme.{u}} {P X Y Z : AlgebraicSpace S}
variable {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

/-- The two legs of a cartesian square of algebraic spaces agree after mapping to points of the
common target. -/
theorem pullbackComparison_condition (h : IsPullback fst snd f g) (p : Points P) :
    map f (map fst p) = map g (map snd p) := sorry

/-- The comparison of points associated to a cartesian square of algebraic spaces. -/
def pullbackComparison (h : IsPullback fst snd f g) : Points P → pullbackObj f g :=
  fun p ↦ ⟨(map fst p, map snd p), pullbackComparison_condition h p⟩

/-- The first component of the points comparison is the map on points induced by `fst`. -/
theorem pullbackComparison_fst (h : IsPullback fst snd f g) (p : Points P) :
    (pullbackComparison h p).1.1 = map fst p := sorry

/-- The second component of the points comparison is the map on points induced by `snd`. -/
theorem pullbackComparison_snd (h : IsPullback fst snd f g) (p : Points P) :
    (pullbackComparison h p).1.2 = map snd p := sorry

/-- The points comparison sends a point of the apex to the compatible pair of its images. -/
theorem pullbackComparison_apply (h : IsPullback fst snd f g) (p : Points P) :
    pullbackComparison h p =
      ⟨(map fst p, map snd p), pullbackComparison_condition h p⟩ := sorry

/-- The comparison of points of a cartesian square of algebraic spaces is surjective. -/
theorem pullbackComparison_surjective (h : IsPullback fst snd f g) :
    Function.Surjective (pullbackComparison h) := sorry

/-- A compatible pair of points of `X` and `Y` over `Z` lifts to a point of a cartesian apex. -/
theorem exists_of_map_eq (h : IsPullback fst snd f g) (x : Points X) (y : Points Y)
    (hxy : map f x = map g y) :
    ∃ p : Points P, map fst p = x ∧ map snd p = y := sorry

end

/-- Specialization of points-comparison surjectivity to a chosen fibre product. -/
theorem pullbackComparison_surjective_of_hasPullback {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    Function.Surjective (pullbackComparison (IsPullback.of_hasPullback f g)) := sorry

end AlgebraicGeometry.AlgebraicSpace.Points
