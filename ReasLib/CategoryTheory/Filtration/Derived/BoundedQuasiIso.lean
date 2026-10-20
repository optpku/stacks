/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.Triangulated
public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded Quasi-isomorphisms of Finite Filtered Complexes

This module owns the restrictions of finite filtered quasi-isomorphisms and finite filtered
acyclic complexes to bounded-below, bounded-above, and bounded homotopy categories.  The actual
localization functors are in `BoundedLocalization` so clients that only need the morphism and
object properties do not import derived-category t-structure infrastructure.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty CategoryTheory.ObjectProperty
open ComplexShape

noncomputable section

universe v u

namespace CategoryTheory

namespace FilteredObject

namespace FiniteDerived

section Restriction

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasCokernels C]
  [CategoryWithHomology (GradedObject ℤ C)]

namespace Plus

/-- Finite filtered quasi-isomorphisms on the bounded-below homotopy category. -/
@[stacks 05S6 "finite filtered bounded quasi-isomorphism"]
abbrev QuasiIso : MorphismProperty (HomotopyCategory.Plus (FilteredObject.Finite.category C)) :=
  (FilteredObject.Finite.Homotopy.quasiIso C).inverseImage (HomotopyCategory.plus (FilteredObject.Finite.category C)).ι

/-- Finite filtered acyclic complexes on the bounded-below homotopy category. -/
@[stacks 05S6 "finite filtered bounded acyclic complex"]
abbrev Acyclic : ObjectProperty (HomotopyCategory.Plus (FilteredObject.Finite.category C)) :=
  (FilteredObject.Finite.Homotopy.acyclic C).inverseImage (HomotopyCategory.plus (FilteredObject.Finite.category C)).ι

namespace QuasiIso

/-- Membership in bounded-below finite filtered quasi-isomorphisms is detected after the ambient
homotopy-category inclusion. -/
@[stacks 05S6 "finite filtered bounded quasi-isomorphism"]
theorem iff {X Y : HomotopyCategory.Plus (FilteredObject.Finite.category C)} (f : X ⟶ Y) :
    Plus.QuasiIso C f ↔
      FilteredObject.Finite.Homotopy.quasiIso C ((HomotopyCategory.plus (FilteredObject.Finite.category C)).ι.map f) := sorry

end QuasiIso

namespace Acyclic

/-- Membership in bounded-below finite filtered acyclic complexes is detected after the ambient
homotopy-category inclusion. -/
@[stacks 05S6 "finite filtered bounded acyclic complex"]
theorem iff (X : HomotopyCategory.Plus (FilteredObject.Finite.category C)) :
    Plus.Acyclic C X ↔
      FilteredObject.Finite.Homotopy.acyclic C ((HomotopyCategory.plus (FilteredObject.Finite.category C)).ι.obj X) := sorry

end Acyclic

end Plus

namespace Minus

/-- Finite filtered quasi-isomorphisms on the bounded-above homotopy category. -/
@[stacks 05S6 "finite filtered bounded quasi-isomorphism"]
abbrev QuasiIso : MorphismProperty (HomotopyCategory.Minus (FilteredObject.Finite.category C)) :=
  (FilteredObject.Finite.Homotopy.quasiIso C).inverseImage (HomotopyCategory.minus (FilteredObject.Finite.category C)).ι

/-- Finite filtered acyclic complexes on the bounded-above homotopy category. -/
@[stacks 05S6 "finite filtered bounded acyclic complex"]
abbrev Acyclic : ObjectProperty (HomotopyCategory.Minus (FilteredObject.Finite.category C)) :=
  (FilteredObject.Finite.Homotopy.acyclic C).inverseImage (HomotopyCategory.minus (FilteredObject.Finite.category C)).ι

namespace QuasiIso

/-- Membership in bounded-above finite filtered quasi-isomorphisms is detected after the ambient
homotopy-category inclusion. -/
@[stacks 05S6 "finite filtered bounded quasi-isomorphism"]
theorem iff {X Y : HomotopyCategory.Minus (FilteredObject.Finite.category C)} (f : X ⟶ Y) :
    Minus.QuasiIso C f ↔
      FilteredObject.Finite.Homotopy.quasiIso C ((HomotopyCategory.minus (FilteredObject.Finite.category C)).ι.map f) := sorry

end QuasiIso

namespace Acyclic

/-- Membership in bounded-above finite filtered acyclic complexes is detected after the ambient
homotopy-category inclusion. -/
@[stacks 05S6 "finite filtered bounded acyclic complex"]
theorem iff (X : HomotopyCategory.Minus (FilteredObject.Finite.category C)) :
    Minus.Acyclic C X ↔
      FilteredObject.Finite.Homotopy.acyclic C ((HomotopyCategory.minus (FilteredObject.Finite.category C)).ι.obj X) := sorry

end Acyclic

end Minus

namespace Bounded

/-- Finite filtered quasi-isomorphisms on the bounded homotopy category. -/
@[stacks 05S6 "finite filtered bounded quasi-isomorphism"]
abbrev QuasiIso : MorphismProperty (HomotopyCategory.Bounded (FilteredObject.Finite.category C)) :=
  (FilteredObject.Finite.Homotopy.quasiIso C).inverseImage (HomotopyCategory.bounded (FilteredObject.Finite.category C)).ι

/-- Finite filtered acyclic complexes on the bounded homotopy category. -/
@[stacks 05S6 "finite filtered bounded acyclic complex"]
abbrev Acyclic : ObjectProperty (HomotopyCategory.Bounded (FilteredObject.Finite.category C)) :=
  (FilteredObject.Finite.Homotopy.acyclic C).inverseImage (HomotopyCategory.bounded (FilteredObject.Finite.category C)).ι

namespace QuasiIso

/-- Membership in bounded finite filtered quasi-isomorphisms is detected after the ambient
homotopy-category inclusion. -/
@[stacks 05S6 "finite filtered bounded quasi-isomorphism"]
theorem iff {X Y : HomotopyCategory.Bounded (FilteredObject.Finite.category C)} (f : X ⟶ Y) :
    Bounded.QuasiIso C f ↔
      FilteredObject.Finite.Homotopy.quasiIso C ((HomotopyCategory.bounded (FilteredObject.Finite.category C)).ι.map f) := sorry

end QuasiIso

namespace Acyclic

/-- Membership in bounded finite filtered acyclic complexes is detected after the ambient
homotopy-category inclusion. -/
@[stacks 05S6 "finite filtered bounded acyclic complex"]
theorem iff (X : HomotopyCategory.Bounded (FilteredObject.Finite.category C)) :
    Bounded.Acyclic C X ↔
      FilteredObject.Finite.Homotopy.acyclic C ((HomotopyCategory.bounded (FilteredObject.Finite.category C)).ι.obj X) := sorry

end Acyclic

end Bounded

end Restriction

section Triangulated

variable (C : Type u) [Category.{v} C] [Abelian C]

namespace Plus.Acyclic

/-- The Verdier morphisms of bounded-below finite filtered acyclic complexes are precisely the
bounded-below finite filtered quasi-isomorphisms. -/
@[stacks 05S6 "finite filtered bounded quasi-isomorphism"]
theorem trW : (Plus.Acyclic C).trW = Plus.QuasiIso C := sorry

end Plus.Acyclic

namespace Minus.Acyclic

/-- The Verdier morphisms of bounded-above finite filtered acyclic complexes are precisely the
bounded-above finite filtered quasi-isomorphisms. -/
@[stacks 05S6 "finite filtered bounded quasi-isomorphism"]
theorem trW : (Minus.Acyclic C).trW = Minus.QuasiIso C := sorry

end Minus.Acyclic

namespace Bounded.Acyclic

/-- The Verdier morphisms of bounded finite filtered acyclic complexes are precisely the bounded
finite filtered quasi-isomorphisms. -/
@[stacks 05S6 "finite filtered bounded quasi-isomorphism"]
theorem trW : (Bounded.Acyclic C).trW = Bounded.QuasiIso C := sorry

end Bounded.Acyclic

end Triangulated

end FiniteDerived

end FilteredObject

end CategoryTheory
