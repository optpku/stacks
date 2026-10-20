/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}}

/-- The relative weak assassin of a scheme module is the locus of points coming from a weakly
associated point of its restriction to some scheme-theoretic fiber. -/
def relativeWeakAss (f : X ⟶ S) (ℱ : X.Modules) : Set X :=
  {x : X | ∃ s : S, ∃ y : Scheme.Hom.fiber f s,
    y ∈ ((Scheme.Modules.pullback (Scheme.Hom.fiberι f s)).obj ℱ).weakAss ∧
      CategoryTheory.ConcreteCategory.hom (Scheme.Hom.fiberι f s).base y = x}

/-- The relative weak assassin is the union of the images of the weak assassins on all
scheme-theoretic fibers. -/
theorem relativeWeakAss_eq_iUnion_image (f : X ⟶ S) (ℱ : X.Modules) :
    relativeWeakAss f ℱ =
      ⋃ s : S,
        Set.image
          (CategoryTheory.ConcreteCategory.hom (Scheme.Hom.fiberι f s).base)
          (((Scheme.Modules.pullback (Scheme.Hom.fiberι f s)).obj ℱ).weakAss) := by
  ext x
  constructor
  · rintro ⟨s, y, hy, rfl⟩
    exact Set.mem_iUnion.2 ⟨s, y, hy, rfl⟩
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨s, hs⟩
    rcases hs with ⟨y, hy, rfl⟩
    exact ⟨s, y, hy, rfl⟩

/-- A point belongs to the relative weak assassin exactly when it is the image of a weakly
associated point of the restriction to some scheme-theoretic fiber. -/
theorem mem_relativeWeakAss_iff (f : X ⟶ S) (ℱ : X.Modules) (x : X) :
    x ∈ relativeWeakAss f ℱ ↔
      ∃ s : S, ∃ y : Scheme.Hom.fiber f s,
        y ∈ ((Scheme.Modules.pullback (Scheme.Hom.fiberι f s)).obj ℱ).weakAss ∧
          CategoryTheory.ConcreteCategory.hom (Scheme.Hom.fiberι f s).base y = x := by
  rfl

end AlgebraicGeometry.Scheme.Modules
