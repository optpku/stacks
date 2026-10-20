/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Module.SectionsWithSupport
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape

@[expose] public section

universe u v w

namespace CategoryTheory.ModuleCat

variable {A : Type u} [CommRing A]

/-- The object property of `A`-modules whose support is contained in `T`. -/
def supportedOn (T : Set (PrimeSpectrum A)) :
    ObjectProperty (ModuleCat.{v} A) :=
  fun M ↦ Module.support A M ⊆ T

/-- Membership in `supportedOn T` is precisely containment of module support in `T`. -/
theorem supportedOn_iff (T : Set (PrimeSpectrum A)) (M : ModuleCat.{v} A) :
    supportedOn T M ↔ Module.support A M ⊆ T := sorry

/-- For a Noetherian ring and specialization-stable `T`, supported modules are exactly those
whose sections with support equal the whole module. -/
theorem supportedOn_iff_sectionsWithSupport_eq_top [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (M : ModuleCat.{v} A) :
    supportedOn T M ↔ Module.sectionsWithSupport T M = ⊤ := sorry

/-- Modules supported on `T` form a Serre class. -/
instance supportedOnIsSerreClass (T : Set (PrimeSpectrum A)) :
    ObjectProperty.IsSerreClass
      (supportedOn T : ObjectProperty (ModuleCat.{v} A)) := sorry

/-- Modules supported on `T` are closed under coproducts indexed by `I`. -/
instance supportedOnIsClosedUnderCoproducts
    (T : Set (PrimeSpectrum A)) (I : Type w) :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (supportedOn T : ObjectProperty (ModuleCat.{v} A)) (Discrete I) := sorry

end CategoryTheory.ModuleCat
