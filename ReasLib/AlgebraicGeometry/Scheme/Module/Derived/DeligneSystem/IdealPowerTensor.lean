/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.InverseSystem
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Tensor.Instances
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.Locality

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.ModuleDerived
open AlgebraicGeometry.RingedSpace.ModuleDerived
open AlgebraicGeometry.RingedSpace.ModuleDerived.Tensor
open AlgebraicGeometry.Scheme.ModuleDerived.ProjectionFormula
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe v

namespace AlgebraicGeometry.Scheme.ModuleDerived

variable {X : Scheme.{v}}

/-- The positive inverse system whose stage `n` is the derived tensor product of `K`
with the degree-zero derived object associated to `I ^ n`. -/
noncomputable def idealPowerTensorSystem (I : X.IdealSheafData)
    (K : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) :
    PNatInverseSystem (DerivedCategory X.Modules) :=
  Modules.IdealPowerProduct.positiveSystem I (𝟙_ X.Modules) ⋙
    DerivedCategory.singleFunctor X.Modules 0 ⋙
      (@curried X.toRingedSpace (hasDerivedTensorBifunctor X)).obj
          ((ambient (SheafOfModules.isCoherent X.ringCatSheaf)).obj K)

/-- The stage `n` of `idealPowerTensorSystem I K` is `K` derived-tensored with the
degree-zero object associated to the module `I ^ n`. -/
theorem idealPowerTensorSystem_stage (I : X.IdealSheafData)
    (K : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) (n : ℕ+) :
    (idealPowerTensorSystem I K).stage n =
      ((@curried X.toRingedSpace (hasDerivedTensorBifunctor X)).obj
          ((ambient (SheafOfModules.isCoherent X.ringCatSheaf)).obj K)).obj
            ((DerivedCategory.singleFunctor X.Modules 0).obj
              (Modules.idealPowerProductSubobject I (𝟙_ X.Modules) n : X.Modules)) := sorry

/-- An ideal whose open complement is the range of an open immersion yields a
Deligne-system presentation of the derived tensor tower of every bounded coherent object. -/
theorem exists_proIso_deligne_idealPowerTensor
    {X U : Scheme.{v}} {j : U ⟶ X}
    [IsNoetherian X] [IsNoetherian U] [IsOpenImmersion j]
    (I : X.IdealSheafData) (hI : I.openComplement = j.opensRange)
    (K : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) :
    ∃ S : DeligneSystem j,
      Nonempty
          ((@Pro.lim (DerivedCategory X.Modules) _ (OrderDual ℕ+) _ _ _ _).obj
              (idealPowerTensorSystem I K) ≅ S.proObject) ∧
        Nonempty
          ((ambient (SheafOfModules.isCoherent U.ringCatSheaf)).obj S.value ≅
            (RingedSpace.modulePullbackDerived j.toShHom).obj
              ((ambient (SheafOfModules.isCoherent X.ringCatSheaf)).obj K)) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
