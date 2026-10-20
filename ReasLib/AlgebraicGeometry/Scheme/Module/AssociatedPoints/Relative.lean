/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}}

/-- The relative assassin of a scheme module is the locus of points coming from an associated
point of its restriction to some scheme-theoretic fiber. -/
def relativeAssassin (f : X ⟶ S) (ℱ : X.Modules) : Set X :=
  {x : X | ∃ s : S, ∃ y : Scheme.Hom.fiber f s,
    y ∈ ((Scheme.Modules.pullback (Scheme.Hom.fiberι f s)).obj ℱ).associatedPoints ∧
      CategoryTheory.ConcreteCategory.hom (Scheme.Hom.fiberι f s).base y = x}

/-- The relative assassin is the union of the images of the associated-point loci on all
scheme-theoretic fibers. -/
theorem relativeAssassin_eq_iUnion_image (f : X ⟶ S) (ℱ : X.Modules) :
    relativeAssassin f ℱ =
      ⋃ s : S,
        Set.image
          (CategoryTheory.ConcreteCategory.hom (Scheme.Hom.fiberι f s).base)
          (((Scheme.Modules.pullback (Scheme.Hom.fiberι f s)).obj ℱ).associatedPoints) := by
  ext x
  constructor
  · rintro ⟨s, y, hy, rfl⟩
    exact Set.mem_iUnion.2 ⟨s, y, hy, rfl⟩
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨s, hs⟩
    rcases hs with ⟨y, hy, rfl⟩
    exact ⟨s, y, hy, rfl⟩

/-- A point belongs to the relative assassin exactly when it is the image of an associated point
of the restriction to some scheme-theoretic fiber. -/
theorem mem_relativeAssassin_iff (f : X ⟶ S) (ℱ : X.Modules) (x : X) :
    x ∈ relativeAssassin f ℱ ↔
      ∃ s : S, ∃ y : Scheme.Hom.fiber f s,
        y ∈ ((Scheme.Modules.pullback (Scheme.Hom.fiberι f s)).obj ℱ).associatedPoints ∧
          CategoryTheory.ConcreteCategory.hom (Scheme.Hom.fiberι f s).base y = x := by
  rfl

end AlgebraicGeometry.Scheme.Modules
