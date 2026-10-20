/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Koszul.PrincipalOpen.Quasicoherent

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open KoszulComplex.PowerTower

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Koszul

/-- If a derived module on an affine scheme has quasi-coherent homology and its
restrictions to a finite union of principal opens vanish in degrees `-r + 1, …, 0`,
then every degree-zero global section factors through a powered Koszul object. -/
theorem exists_poweredStage_lift {A : Type u} [CommRing A] {r : ℕ}
    (f : Fin r → A)
    (E : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty (Spec (CommRingCat.of A)).toRingedSpace))
    (hE : ∀ i : ℤ, -(r : ℤ) + 1 ≤ i → i ≤ 0 →
      IsZero
        ((moduleRestrictionToOpen (Spec (CommRingCat.of A)).toRingedSpace
          (Scheme.PrincipalOpenCech.openSubset f)).obj
            ((DerivedCategory.homologyFunctor
              (Spec (CommRingCat.of A)).toRingedSpace.Modules i).obj E.obj)))
    (s : affineUnitDerived A ⟶ E.obj) :
    ∃ e : ℕ,
      ∃ g : (affineDerivedTilde A).obj (derivedStage f e) ⟶ E.obj,
        ((affineDerivedTilde A).map
          (DerivedCategory.Q.map (Fin.unitComponent f e)) :
            affineUnitDerived A ⟶ (affineDerivedTilde A).obj (derivedStage f e)) ≫ g = s := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.Koszul
