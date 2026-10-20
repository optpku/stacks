/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Domain
public import ReasLib.CategoryTheory.Functor.Derived.Definedness.Left
public import ReasLib.CategoryTheory.Functor.Derived.Definedness.Right
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived-value functors on essential-constancy domains

The stronger source-definedness domain maps canonically to Mathlib's pointwise-existence domain.
Composing that inclusion with the pointwise-value functor packages the selected derived values on
the full domain where the localization-indexed diagram is essentially constant.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']

namespace RightDerived.DefinedAt

/-- The pointwise right-derived values assembled on the essential-constancy domain. -/
@[stacks 05SC "right-derived functor on its essential-constancy domain"]
noncomputable def functor (F : D ⥤ D') (S : MorphismProperty D) :
    Domain F S ⥤ D' :=
  Domain.toPointwise F S ⋙ RightDerived.Definedness.functor F S

namespace functor

/-- The source-defined right-derived functor evaluates to the canonical pointwise value. -/
@[simp, stacks 05SC "right-derived essential-constancy-domain functor on objects"]
theorem obj (F : D ⥤ D') (S : MorphismProperty D) (X : Domain F S) :
    (functor F S).obj X = RightDerived.Value.obj F S X.obj := sorry

/-- The source-defined right-derived functor maps a morphism by the canonical pointwise-value
map. -/
@[simp, stacks 05SC "right-derived essential-constancy-domain functor on morphisms"]
theorem map (F : D ⥤ D') (S : MorphismProperty D)
    {X Y : Domain F S} (f : X ⟶ Y) :
    (functor F S).map f = RightDerived.Value.map F S f.hom := sorry

end functor

end RightDerived.DefinedAt

namespace LeftDerived.DefinedAt

/-- The pointwise left-derived values assembled on the essential-constancy domain. -/
@[stacks 05SC "left-derived functor on its essential-constancy domain"]
noncomputable def functor (F : D ⥤ D') (S : MorphismProperty D) :
    Domain F S ⥤ D' :=
  Domain.toPointwise F S ⋙ LeftDerived.Definedness.functor F S

namespace functor

/-- The source-defined left-derived functor evaluates to the canonical pointwise value. -/
@[simp, stacks 05SC "left-derived essential-constancy-domain functor on objects"]
theorem obj (F : D ⥤ D') (S : MorphismProperty D) (X : Domain F S) :
    (functor F S).obj X = LeftDerived.Value.obj F S X.obj := sorry

/-- The source-defined left-derived functor maps a morphism by the canonical pointwise-value
map. -/
@[simp, stacks 05SC "left-derived essential-constancy-domain functor on morphisms"]
theorem map (F : D ⥤ D') (S : MorphismProperty D)
    {X Y : Domain F S} (f : X ⟶ Y) :
    (functor F S).map f = LeftDerived.Value.map F S f.hom := sorry

end functor

end LeftDerived.DefinedAt

end CategoryTheory.Functor
