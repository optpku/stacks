/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CompactSupport.OrdinaryColimit

/-! A bounded coherent extension of the actual source input is selected from
the existing normalized Deligne owner. Its restriction comparison is constructed
from that owner's specified constant restriction; no extension iso is an input. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport

open DeligneSystem

variable {X U : Scheme.{u}} [IsNoetherian X] [IsNoetherian U]
variable (j : U ⟶ X) [IsOpenImmersion j]

/-- The first bounded coherent stage of the chosen Deligne extension of K. -/
def sourceExtension (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]) :
    Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf] :=
  (boundedTower j (extension j K)).obj (1 : OrderDual ℕ+)

/-- The actual source extension restricts to K through the normalized
Deligne restriction and its value identification. -/
def sourceExtensionIso (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]) :
    (restriction j).obj (sourceExtension j K) ≅ K :=
  (ambient (SheafOfModules.isCoherent U.ringCatSheaf)).preimageIso
    ((restrictionAmbientIso j).app (sourceExtension j K) ≪≫
      (RingedSpace.modulePullbackDerived j.toShHom).mapIso
        ((boundedTowerAmbientIso j (extension j K)).app (1 : OrderDual ℕ+)) ≪≫
      (extension j K).restrictionIso.app (1 : OrderDual ℕ+) ≪≫
      (ambient (SheafOfModules.isCoherent U.ringCatSheaf)).mapIso
        (eqToIso (extension_value j K)))

/-- The ambient comparison to K has exactly the actual restricted source
extension as its domain. -/
def sourceExtensionAmbientIso (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]) :
    (RingedSpace.modulePullbackDerived j.toShHom).obj (sourceExtension j K).obj.obj ≅ K.obj.obj :=
  (restrictionAmbientIso j).symm.app (sourceExtension j K) ≪≫
    (ambient (SheafOfModules.isCoherent U.ringCatSheaf)).mapIso (sourceExtensionIso j K)

end AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport
