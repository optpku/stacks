module

public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import stacks_project.Chap61.Definition_61_29_1_Derived
public import stacks_project.Chap61.Lemma_61_19_11_Reduction
public import stacks_project.Chap61.Lemma_61_19_8_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Boundedness and étale origin of pro-étale reductions

Source-facing predicates for the reductions `K ⊗^L underline(Λ ⧸ I^n)` used by
proper base change: bounded below in `D(X_proétale, Λ ⧸ I^n)`, and cohomology
sheaves in the essential image of `ε⁻¹`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.DerivedCategory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProetaleDerived

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
variable [HasWeakSheafify (ProEt.topology X) (ModuleCat.{u + 1} Λ)]
variable [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} Λ)]
variable [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))]
variable [CategoryWithHomology (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))]

/-- Underlying derived object of a pro-étale derived complex. -/
@[irreducible]
def toDerivedCategory (K : ProetaleDerived X Λ) :
    DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) :=
  K

/-- `toDerivedCategory` is the identity on the underlying derived category. -/
theorem toDerivedCategory_eq (K : ProetaleDerived X Λ) :
    toDerivedCategory K =
      (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))) :=
  sorry

/-- The reduction `K ⊗^L underline(Λ ⧸ I^n)` is bounded below in
`D(X_proétale, Λ ⧸ I^n)`. -/
@[irreducible]
def IsProEtReductionBoundedBelow (I : Ideal Λ) (n : ℕ)
    [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ n))]
    [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ n)))]
    [(proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ n)) X).Additive]
    [(Functor.Homotopy.toDerived
        (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ n)) X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) (ComplexShape.up ℤ))]
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))) : Prop :=
  IsBoundedBelow
    (proEtReduction I n K :
      DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ n))))

/-- `IsProEtReductionBoundedBelow` is boundedness of `proEtReduction`. -/
theorem isProEtReductionBoundedBelow_iff (I : Ideal Λ) (n : ℕ)
    [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ n))]
    [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ n)))]
    [(proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ n)) X).Additive]
    [(Functor.Homotopy.toDerived
        (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ n)) X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) (ComplexShape.up ℤ))]
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))) :
    IsProEtReductionBoundedBelow I n K ↔
      IsBoundedBelow
        (proEtReduction I n K :
          DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ n)))) :=
  sorry

/-- The cohomology sheaves of `K ⊗^L underline(Λ ⧸ I^n)` come from `X_étale`. -/
@[irreducible]
def IsProEtReductionCohomologyFromEtale (I : Ideal Λ) (n : ℕ)
    [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ n))]
    [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ n)))]
    [(proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ n)) X).Additive]
    [(Functor.Homotopy.toDerived
        (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ n)) X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) (ComplexShape.up ℤ))]
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I ^ n))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I ^ n)))]
    [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (Λ ⧸ I ^ n),
      (etaleToProEt X).op.HasLeftKanExtension F]
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))) : Prop :=
  cohomologyIn (etaleToProEtModuleEssImage X (Λ ⧸ I ^ n))
    (proEtReduction I n K :
      DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ n))))

/-- `IsProEtReductionCohomologyFromEtale` is the étale-origin condition on
`proEtReduction`. -/
theorem isProEtReductionCohomologyFromEtale_iff (I : Ideal Λ) (n : ℕ)
    [HasSheafify (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ n))]
    [HasDerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ n)))]
    [(proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ n)) X).Additive]
    [(Functor.Homotopy.toDerived
        (proEtModuleExtendScalars (Ideal.Quotient.mk (I ^ n)) X)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)) (ComplexShape.up ℤ))]
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I ^ n))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I ^ n)))]
    [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (Λ ⧸ I ^ n),
      (etaleToProEt X).op.HasLeftKanExtension F]
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))) :
    IsProEtReductionCohomologyFromEtale I n K ↔
      cohomologyIn (etaleToProEtModuleEssImage X (Λ ⧸ I ^ n))
        (proEtReduction I n K :
          DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (Λ ⧸ I ^ n)))) :=
  sorry

end AlgebraicGeometry.Scheme

end

end
