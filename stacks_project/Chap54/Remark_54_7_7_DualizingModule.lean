/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DualizingModule
public import ReasLib.AlgebraicGeometry.Scheme.Module.Dualizing

@[expose] public section

open CategoryTheory

universe u

namespace ModuleCat

/-- Compatibility view of the intrinsic dualizing-module predicate with the historical
closed-monoidal argument retained for source-facing consumers. -/
def IsDualizing {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ω : ModuleCat.{u} A) : Prop :=
  IsDualizingModule ω

end ModuleCat

#check (@ModuleCat.IsDualizing :
  {A : Type u} → [CommRing A] → [IsNoetherianRing A] →
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))] →
    MonoidalClosed (DerivedCategory (ModuleCat.{u} A)) →
    ModuleCat.{u} A → Prop)

#check (@ModuleCat.IsDualizingModule :
  {A : Type u} → [CommRing A] → [IsNoetherianRing A] → ModuleCat.{u} A → Prop)
