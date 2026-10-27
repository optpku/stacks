/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.GlobalSections.Obstruction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.DerivedBaseChange

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.GlobalSections

/-- The spectrum of the base ring. -/
abbrev S (Λ : Type u) [CommRing Λ] : Scheme.{u} := Spec (CommRingCat.of Λ)

/- Example 98.22.3. The obstruction functor sends a module to first cohomology of its tensor sheaf. -/
#check (AlgebraicGeometry.GroupoidsOver.GlobalSections.obstructionModule :
  ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    {W : Scheme.{u}} (w : W ⟶ S Λ) (F : W.Modules)
    (A : Type u) [CommRing A] [Algebra Λ A], ModuleCat A ⥤ ModuleCat A)

end AlgebraicGeometry.GroupoidsOver.GlobalSections
