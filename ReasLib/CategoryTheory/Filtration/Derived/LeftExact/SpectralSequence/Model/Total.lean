/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Model.Construction
public import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective.Resolution.Total

/-!
# Total-category functor for finite filtered right-derived models

This leaf assembles the filtered models attached to strict filtered-injective resolutions into a
functor on the total resolution category.  Both object and morphism data are inherited directly
from the selected resolution, so the construction introduces no additional choices.
-/

@[expose] public section

open CategoryTheory ComplexShape
open CochainComplex.FilteredInjectivePlus

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Model

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B]

/-- The choice-free functor from total strict filtered-injective resolutions to their finite
filtered models after applying a left-exact functor degreewise.  It first retains the resolving
complex, then forgets its termwise filtered-injective property, and finally applies the finite
filtered model functor. -/
@[stacks 015W "functorial finite filtered right-derived model"]
noncomputable abbrev functor (T : A ⥤ₗ B) :
    Resolution.Total A ⥤ FilteredComplex B :=
  Resolution.Total.target A ⋙
    _root_.CochainComplex.FilteredInjectivePlus.ι A ⋙ modelFunctor T

/-- Object computation for the functorial finite filtered right-derived model. -/
@[simp, stacks 015W "functorial finite filtered right-derived model computation"]
theorem functor_obj (T : A ⥤ₗ B)
    (X : Resolution.Total A) :
    (functor T).obj X = model T X.obj := sorry

/-- Morphism computation for the functorial finite filtered right-derived model. -/
@[simp, stacks 015W "functorial finite filtered right-derived model computation"]
theorem functor_map (T : A ⥤ₗ B)
    {X Y : Resolution.Total A} (f : X ⟶ Y) :
    (functor T).map f = modelMap T f.displayed := sorry

end CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Model
