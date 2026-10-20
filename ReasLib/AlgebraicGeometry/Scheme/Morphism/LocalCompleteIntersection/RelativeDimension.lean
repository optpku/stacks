/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Koszul

/-!
# Local complete intersections of signed relative dimension

This file records the virtual relative dimension of a local complete-intersection morphism
using local Koszul-regular immersions followed by smooth morphisms.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A local complete-intersection morphism has virtual relative dimension `r : ℤ` when it
locally factors as a Koszul-regular immersion of conormal rank `c` followed by a smooth
morphism of relative dimension `n`, with `n - c = r`. -/
def LocalCompleteIntersectionOfRelativeDimension
    {X Y : Scheme.{u}} (f : X ⟶ Y) (r : ℤ) : Prop :=
  LocallyOfType RingHom.IsLocalCompleteIntersection f ∧
    ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∃ (P : Scheme.{u}) (i : U.toScheme ⟶ P) (π : P ⟶ Y) (n c : ℕ),
        IsKoszulRegularImmersion i ∧ SmoothOfRelativeDimension n π ∧
          Scheme.Modules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i) ∧
          i ≫ π = U.ι ≫ f ∧ (n : ℤ) - (c : ℤ) = r

/-- The local complete-intersection condition and the complete numerical presentation
condition defining virtual relative dimension `r`. -/
theorem localCompleteIntersectionOfRelativeDimension_iff
    {X Y : Scheme.{u}} (f : X ⟶ Y) (r : ℤ) :
    LocalCompleteIntersectionOfRelativeDimension f r ↔
      LocallyOfType RingHom.IsLocalCompleteIntersection f ∧
        ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
          ∃ (P : Scheme.{u}) (i : U.toScheme ⟶ P) (π : P ⟶ Y) (n c : ℕ),
            IsKoszulRegularImmersion i ∧ SmoothOfRelativeDimension n π ∧
              Scheme.Modules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i) ∧
              i ≫ π = U.ι ≫ f ∧ (n : ℤ) - (c : ℤ) = r := sorry

/-- A regular immersion with conormal rank `c` is a local complete-intersection morphism of
virtual relative dimension `-c`. -/
theorem localCompleteIntersectionOfRelativeDimension_of_regularImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) (c : ℕ) [IsRegularImmersion f]
    [Scheme.Modules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf f)] :
    LocalCompleteIntersectionOfRelativeDimension f (-(c : ℤ)) := sorry

end AlgebraicGeometry
