/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Grothendieck
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pushforward.Additive
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Injective
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Cochain
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-Below Derived Pushforward on Ringed Spaces

This file specializes the canonical bounded-below right-derived functor to direct image of
module sheaves. The public API hides the homotopy localization and quasi-isomorphism denominator,
which are implementation details already owned by the generic bounded right-derived API.
-/

@[expose] public section

open AlgebraicGeometry.RingedSpace.Hom

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The bounded-below total right-derived pushforward of module sheaves along a morphism of
ringed spaces. -/
@[stacks 05S9 "bounded-below total right-derived pushforward", stacks 0718
  "20.3.0.4: bounded-below derived direct image"]
abbrev moduleDerivedPushforwardPlus
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    DerivedCategory.Plus X.Modules ⥤ DerivedCategory.Plus Y.Modules :=
  Functor.RightDerived.Bounded.functor (pushforward f)

namespace moduleDerivedPushforwardPlus

/-- The canonical localization unit for bounded-below derived pushforward. -/
@[stacks 05S9 "bounded-below derived-pushforward unit", stacks 0718
  "20.3.0.4: bounded-below derived direct-image unit"]
noncomputable abbrev unit
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (pushforward f).toBoundedBelowDerived ⟶
      DerivedCategory.Plus.Qh ⋙ moduleDerivedPushforwardPlus f :=
  Functor.RightDerived.Bounded.unit (pushforward f)

/-- Degree-`n` cohomology after bounded-below total right-derived pushforward. -/
@[stacks 05S9 "bounded-below derived-pushforward cohomology", stacks 0718
  "20.3.0.4: bounded-below derived direct-image cohomology"]
abbrev cohomologyFunctor
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (n : ℤ) :
    DerivedCategory.Plus X.Modules ⥤ Y.Modules :=
  moduleDerivedPushforwardPlus f ⋙ DerivedCategory.Plus.homologyFunctor Y.Modules n

/-- The degree-`n` cohomology object of the bounded-below derived pushforward. -/
@[stacks 05S9 "bounded-below derived-pushforward cohomology", stacks 0718
  "20.3.0.4: bounded-below derived direct-image cohomology object"]
abbrev cohomology
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    (K : DerivedCategory.Plus X.Modules) (n : ℤ) : Y.Modules :=
  (cohomologyFunctor f n).obj K

end moduleDerivedPushforwardPlus

end AlgebraicGeometry.RingedSpace
