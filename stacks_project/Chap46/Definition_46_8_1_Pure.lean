/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Pure

@[expose] public section

universe u v

variable {R : Type u} [CommRing R]

/- Compatibility check for the shared pure-projective module predicate. -/
#check (ModuleCat.PureProjective : ModuleCat.{v} R → Prop)

/- Compatibility check for the shared pure-injective module predicate. -/
#check (ModuleCat.PureInjective : ModuleCat.{v} R → Prop)
