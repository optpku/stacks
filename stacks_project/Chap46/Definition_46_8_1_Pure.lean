/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
