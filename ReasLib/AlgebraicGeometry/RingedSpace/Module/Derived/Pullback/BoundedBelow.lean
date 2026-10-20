/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatMorphism
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Grothendieck
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.RightDerived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-below derived pullback along a flat morphism

Flat pullback is exact, so its bounded-below derived action is the direct action of a bundled exact
functor.  The flatness assumption is kept on the public owner because a general pullback need not
preserve the intended exact model.
-/

@[expose] public section

open AlgebraicGeometry.RingedSpace.Hom

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

-- Reuse additivity supplied by the existing exact flat-pullback owner.
instance flatPullback_additive {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [RingedSpace.Hom.IsFlat f] : (pullback f).Additive :=
  ExactFunctor.additive (RingedSpace.Hom.IsFlat.exactPullback f)

/-- The bounded-below derived pullback of module sheaves along a flat morphism of ringed spaces.
-/
@[stacks 02N7 "bounded-below flat derived pullback"]
abbrev moduleDerivedPullbackPlus
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) [RingedSpace.Hom.IsFlat f] :
    DerivedCategory.Plus Y.Modules ⥤ DerivedCategory.Plus X.Modules :=
  ExactFunctor.Derived.Plus.functor (RingedSpace.Hom.IsFlat.exactPullback f)

namespace moduleDerivedPullbackPlus

/-- The localization factorization identifying flat pullback with its direct bounded-below
derived action. -/
@[stacks 02N7 "bounded-below flat pullback factorization"]
noncomputable abbrev factorIso
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) [RingedSpace.Hom.IsFlat f] :
    (pullback f).toBoundedBelowDerived ≅
      DerivedCategory.Plus.Qh ⋙ moduleDerivedPullbackPlus f :=
  ExactFunctor.Derived.Plus.factorIso (RingedSpace.Hom.IsFlat.exactPullback f)

/-- The canonical localization unit for bounded-below flat derived pullback. -/
@[stacks 02N7 "bounded-below flat derived-pullback unit"]
noncomputable abbrev unit
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) [RingedSpace.Hom.IsFlat f] :
    (pullback f).toBoundedBelowDerived ⟶
      DerivedCategory.Plus.Qh ⋙ moduleDerivedPullbackPlus f :=
  (factorIso f).hom

end moduleDerivedPullbackPlus

end AlgebraicGeometry.RingedSpace
