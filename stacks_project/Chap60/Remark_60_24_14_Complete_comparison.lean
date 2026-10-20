module

public import stacks_project.Chap60.Remark_60_24_14_Complete_comparison_StableBase
public import stacks_project.Chap60.Remark_60_24_14_Complete_comparison_Geometry
public import stacks_project.Chap60.Remark_60_24_14_Complete_comparison_Stage
public import stacks_project.Chap60.Remark_60_24_14_Complete_comparison_DeRham
public import stacks_project.Chap60.Remark_60_24_14_Complete_comparison_ConnectionReduction
public import stacks_project.Chap60.Remark_60_24_14_Complete_comparison_CrystallineSections
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf CrystallineCoefficients CrystallineSmoothLiftTerms
open CrystallineCompleteStages CrystallineCompleteConnection CrystallineCompleteReduction
open CrystallineCompleteSections

universe u

namespace CrystallineCompleteComparison

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable [hNoetherian : IsNoetherianRing A]
variable [hComplete : IsAdicComplete (Ideal.span {(p : A)}) A]
variable {IA : Ideal A} (γA : DividedPowers IA)
variable {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [hSmooth : Smooth f] [hProper : IsProper f]
variable (I : (Spec (.of A)).IdealSheafData)
variable (γS : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (I.ideal V))
variable (hc : ∀ (V : (Spec (.of A)).affineOpens) (a : Γ(Spec (.of A), V)),
  (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen a))
    ((Spec (.of A)).presheaf.map (homOfLE ((Spec (.of A)).basicOpen_le a)).op).hom)
variable (hI : specIdealEqOfIdealTop IA I) (hγ : specDividedPowersEq IA γA I γS)
variable (hpI : IsNilpotent (Ideal.Quotient.mk IA (p : A)))
variable (F : CrisModuleSheaf (Spec (.of A)) I γS hc (smoothLift f I) (smoothLift_x₀ f I))
variable [SectionsCoherent I γS hc (smoothLift_x₀ f I) F]
variable [CrisModuleSheaf.IsCrystal F] [hqc : CrisModuleSheaf.IsLocallyQuasiCoherent F]

variable (hft : ∀ Aobj, (F.obj Aobj).IsFiniteType)

include hft hNoetherian hComplete hSmooth hProper hqc in
/-- Remark 60.24.14 (Complete comparison) (1): a finite type quasi-coherent
crystal algebraizes to a coherent module with an integrable connection.
Leibniz is required before integrability is formed. Its quotient connections
are compatibly identified with the crystal evaluations on the cofinal
PD-stable p-power stages; this tail determines the p-adic system. -/
@[stacks 07MZ]
theorem exists_algebraizedConnection :
    ∃ (FY : Y.Modules) (hcoh : FY.IsCoherent)
      (nabla : asBaseSheaf f FY ⟶ asBaseSheaf f (oneFormTensor f FY))
      (hconn : IsConnection f FY nabla) (hnabla : IsIntegrable f FY nabla)
      (hred : ReductionSystem γA f I γS hc hI hγ hpI F FY nabla),
      True := sorry

variable (s : Spec (.of A) ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))

include hft hNoetherian hComplete hSmooth hProper hqc in
/-- Remark 60.24.14 (Complete comparison) (2): crystalline derived global
sections are isomorphic in D(A) to the sheaf de Rham derived global sections
of a coherent algebraization. Compatibility of the reductions supplies a
single inverse system, rather than unrelated stagewise isomorphisms. -/
@[stacks 07MZ]
theorem crystalline_deRham_comparison (FY : Y.Modules) [FY.IsCoherent]
    (nabla : asBaseSheaf f FY ⟶ asBaseSheaf f (oneFormTensor f FY))
    [IsConnection f FY nabla] (hnabla : IsIntegrable f FY nabla)
    (hred : ReductionSystem γA f I γS hc hI hγ hpI F FY nabla)
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1}
      (liftedRingedSite I γS hc (smoothLift_x₀ f I) p s
        (pNilpotentOnClosedFibre p f I hI hpI)))]
    [HasSheafify (Opens.grothendieckTopology Y.toTopCat) (ModuleCat.{u + 1} A)]
    [HasGlobalSectionsFunctor (Opens.grothendieckTopology Y.toTopCat)
      (ModuleCat.{u + 1} A)]
    [IsGrothendieckAbelian
      (Sheaf (Opens.grothendieckTopology Y.toTopCat) (ModuleCat.{u + 1} A))] :
    IsIsomorphic (crystallineSections p f I γS hc hI hpI F s)
      (deRhamSections f FY nabla hnabla) := sorry

end CrystallineCompleteComparison
