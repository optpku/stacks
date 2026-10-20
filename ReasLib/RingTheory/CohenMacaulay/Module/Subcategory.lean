module

public import ReasLib.RingTheory.CohenMacaulay.Module
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open scoped ENat

universe u

namespace ModuleCat

/-- Finite Cohen-Macaulay `A`-modules whose depth is the natural number `d`. -/
def cohenMacaulayOfDepth
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (d : ℕ) :
    ObjectProperty (ModuleCat.{u} A) :=
  fun M ↦ Module.CohenMacaulay A M ∧ moduleDepth A M = (d : ℕ∞)

/-- Membership in `cohenMacaulayOfDepth A d` records Cohen-Macaulayness and depth `d`. -/
theorem cohenMacaulayOfDepth_iff
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (d : ℕ) (M : ModuleCat.{u} A) :
    cohenMacaulayOfDepth A d M ↔
      Module.CohenMacaulay A M ∧ moduleDepth A M = (d : ℕ∞) := sorry

end ModuleCat
