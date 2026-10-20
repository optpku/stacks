/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.Triangulated
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.InverseSystem.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.InverseSystem

/-!
# A cohomological criterion for Deligne systems

This module characterizes bounded positive inverse systems that present the pro-object of a
Deligne system in terms of their stagewise cohomology systems.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe v

namespace AlgebraicGeometry.Scheme.ModuleDerived

open AlgebraicGeometry.Scheme.Modules

variable {X U : Scheme.{v}} {j : U ⟶ X}
variable [IsNoetherian X] [IsNoetherian U] [IsOpenImmersion j]

/-- A bounded-amplitude positive inverse system of bounded coherent derived objects presents
the pro-object of a Deligne system exactly when each cohomology system presents an ideal-power
pro-object for a coherent module, using a fixed ideal cutting out the open complement. -/
theorem exists_proIso_deligne_iff_cohomology
    (a b : ℤ) (hab : a ≤ b)
    (I : X.IdealSheafData) (hI : I.openComplement = j.opensRange)
    (K : PNatInverseSystem
      (@DerivedCategory.Bounded.CohomologyIn X.Modules _ _
        (AlgebraicGeometry.Scheme.Modules.schemeModulesHasDerivedCategory X)
        (SheafOfModules.isCoherent X.ringCatSheaf)))
    (hK : ∀ n : ℕ+, ∀ i : ℤ, i ∉ Set.Icc a b →
      IsZero ((BoundedSystem.cohomology K i).stage n)) :
    (∃ S : DeligneSystem j, Nonempty (boundedProObject K ≅ S.proObject)) ↔
      ∀ p : ℤ,
        ∃ F : (SheafOfModules.isCoherent X.ringCatSheaf).FullSubcategory,
          Nonempty
            ((@Pro.lim X.Modules _ (OrderDual ℕ+) _ _ _ _).obj
                (BoundedSystem.cohomology K p) ≅
              (@Pro.lim X.Modules _ (OrderDual ℕ+) _ _ _ _).obj
                (IdealPowerProduct.positiveSystem I F.obj)) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
