/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.IdealPowerTensor
import StacksCheckRecall

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

variable {X U : Scheme.{v}} {j : U ⟶ X}
variable [IsNoetherian X] [IsNoetherian U] [IsOpenImmersion j]

/- Lemma 48.30.11: for an ideal sheaf `I` cutting out the complement of the open
immersion `j : U ⟶ X` and `K ∈ Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]`, the
positive system `K ⊗ᴸ I ^ n` is pro-isomorphic to a Deligne system whose constant
value over `U` is the derived restriction of `K`. -/
@[stacks 0G4U] #check (@AlgebraicGeometry.Scheme.ModuleDerived.exists_proIso_deligne_idealPowerTensor :
    ∀ {X U : Scheme.{v}} {j : U ⟶ X} [IsNoetherian X] [IsNoetherian U]
      [IsOpenImmersion j]
      (I : X.IdealSheafData) (hI : I.openComplement = j.opensRange)
      (K : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]),
      ∃ S : DeligneSystem j,
        Nonempty
            ((@Pro.lim (DerivedCategory X.Modules) _ (OrderDual ℕ+) _ _ _ _).obj
                (AlgebraicGeometry.Scheme.ModuleDerived.idealPowerTensorSystem I K) ≅
              S.proObject) ∧
          Nonempty
            ((ambient (SheafOfModules.isCoherent U.ringCatSheaf)).obj S.value ≅
              (RingedSpace.modulePullbackDerived j.toShHom).obj
                ((ambient (SheafOfModules.isCoherent X.ringCatSheaf)).obj K)))
