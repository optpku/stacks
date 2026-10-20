module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.OfModule

/-!
# Square-zero first-order thickenings associated to modules

This source-facing module preserves the historical API through typed checks of
the canonical square-zero constructions.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.RingedSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RingedSpace.IsFirstOrderThickening

#check (ofModuleSpace : ∀ {X : RingedSpace.{u}}, X.Modules → RingedSpace.{u})
#check (inclusion : ∀ {X : RingedSpace.{u}} (M : X.Modules),
  X ⟶ ofModuleSpace M)
#check (retraction : ∀ {X : RingedSpace.{u}} (M : X.Modules),
  ofModuleSpace M ⟶ X)
#check (ofModule : ∀ {X : RingedSpace.{u}} (M : X.Modules), Trivialized X)
#check (ofModuleMap : ∀ {X : RingedSpace.{u}} {M N : X.Modules},
  (N ⟶ M) → Trivialized.Hom (ofModule M) (ofModule N))

end AlgebraicGeometry.RingedSpace.IsFirstOrderThickening
