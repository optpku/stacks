/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.TensorPower
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Numerical
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.OpenImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.ClosedImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-! # Numerical substacks for finite tensor-power families -/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack.Numerical

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- For a separated morphism of finite presentation and a finite list of perfect derived
 modules, the inclusion of the substack with prescribed tensor-power numerical invariants
 is an open immersion. -/
instance instOpenImmersionTensorPower (f : X ⟶ B)
    [FinitePresentation f] [Separated f] {r : ℕ}
    (E : Fin r → ModuleDerived X) (hE : ∀ i, ModuleDerived.IsPerfect (E i))
    (P : tensorPowerIndex r → ℤ) :
    CohStack.OpenImmersion
      (ι f (tensorPowerFamily E) P (fun n ↦ isPerfect_tensorPowerFamily E hE n)) := sorry

/-- For a separated morphism of finite presentation and a finite list of perfect derived
 modules, the inclusion of the substack with prescribed tensor-power numerical invariants
 is a closed immersion. -/
instance instClosedImmersionTensorPower (f : X ⟶ B)
    [FinitePresentation f] [Separated f] {r : ℕ}
    (E : Fin r → ModuleDerived X) (hE : ∀ i, ModuleDerived.IsPerfect (E i))
    (P : tensorPowerIndex r → ℤ) :
    Hom.ClosedImmersion
      (ι f (tensorPowerFamily E) P (fun n ↦ isPerfect_tensorPowerFamily E hE n)) := sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack.Numerical
