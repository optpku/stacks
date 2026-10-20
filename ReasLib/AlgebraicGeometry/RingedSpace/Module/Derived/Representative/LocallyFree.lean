/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Bounded.Local
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree

/-!
# Locally bounded finite locally free representatives

This file records the property that a derived module on a ringed space has one global
cochain-complex representative which is locally bounded in both directions and termwise finite
locally free.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X : RingedSpace.{u}}

/-- Derived modules admitting a global cochain-complex representative which is locally bounded
above and below and finite locally free in every degree. -/
def locallyBoundedFiniteLocallyFreeRepresentative : ObjectProperty (ModuleDerived X) :=
  fun M ↦ ∃ P : CochainComplex X.Modules ℤ,
    IsIsomorphic (DerivedCategory.Q.obj P) M ∧
      CochainComplex.IsLocallyBoundedAbove P ∧
      CochainComplex.IsLocallyBoundedBelow P ∧
      ∀ i : ℤ, (SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) :
        ObjectProperty X.Modules) (P.X i)

/-- A derived module has a locally bounded finite locally free representative when it belongs to
`locallyBoundedFiniteLocallyFreeRepresentative`. -/
abbrev HasLocallyBoundedFiniteLocallyFreeRepresentative (M : ModuleDerived X) : Prop :=
  locallyBoundedFiniteLocallyFreeRepresentative M

/-- The expanded characterization of a derived module admitting a locally bounded finite locally
free representative. -/
theorem hasLocallyBoundedFiniteLocallyFreeRepresentative_iff (M : ModuleDerived X) :
    HasLocallyBoundedFiniteLocallyFreeRepresentative M ↔
      ∃ P : CochainComplex X.Modules ℤ,
        IsIsomorphic (DerivedCategory.Q.obj P) M ∧
          CochainComplex.IsLocallyBoundedAbove P ∧
          CochainComplex.IsLocallyBoundedBelow P ∧
          ∀ i : ℤ,
            (SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) :
              ObjectProperty X.Modules) (P.X i) := sorry

/-- Admitting a locally bounded finite locally free representative is invariant under
isomorphisms of derived modules. -/
instance locallyBoundedFiniteLocallyFreeRepresentative_isClosedUnderIsomorphisms :
    (locallyBoundedFiniteLocallyFreeRepresentative (X := X)).IsClosedUnderIsomorphisms := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived
