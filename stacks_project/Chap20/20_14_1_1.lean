/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Pushforward.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Pushforward.Bounded
import StacksCheckRecall

@[expose] public section

/-!
# The derived global-sections map of an f-map

The map is owned by the bounded-below, module-valued change-of-space API for derived global
sections.  Its construction first accepts a morphism into bounded-below derived pushforward and
then specializes to an ordinary `f`-map; restriction of scalars to `Γ(Y, 𝒪_Y)` is part of that
owner.
-/

/- Equation 20.14.1.1: an `f`-map `G ⟶ f_*F` induces the canonical map
`RΓ(Y, G) ⟶ RΓ(X, F)`. -/
@[stacks 01F9]
#check @AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Bounded.mapOfFMap

/- Equivalently, after explicitly applying derived extension of scalars, the same semilinear
map has a `Γ(X, 𝒪_X)`-linear adjoint in the unbounded derived category.  Without a Tor-dimension
hypothesis, this companion need not preserve bounded-below objects. -/
#check @AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Adjoint.mapOfFMap

/- The adjunction specification recovers the canonical restricted-scalar map. -/
#check @AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Adjoint.mapOfFMap_adjunct

/- The construction is defined more generally for a morphism into bounded-below derived
pushforward. -/
#check @AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Bounded.mapOfPushforward

/- The ordinary `f`-map enters through the canonical single-complex pushforward comparison. -/
#check @AlgebraicGeometry.RingedSpace.moduleDerivedPushforwardPlus.comparison

/- Derived sections commute with direct image after the canonical restriction of scalars. -/
#check @AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Bounded.pushforwardIso
