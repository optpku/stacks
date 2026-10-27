/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Completed.SmoothLiftComparison
import StacksCheckRecall

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline
open AlgebraicGeometry.Scheme.Modules.DeRham
open CrystallineModuleSheaf

universe u

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable [hNoetherian : IsNoetherianRing A]
variable [hComplete : IsAdicComplete (Ideal.span {(p : A)}) A]
variable {IA : Ideal A} (γA : DividedPowers IA)
variable {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [hSmooth : Smooth f] [hProper : IsProper f]
variable (I : (Spec (.of A)).IdealSheafData)
variable (γS : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (I.ideal V))
variable (hc : ∀ (V : (Spec (.of A)).affineOpens) (a : Γ(Spec (.of A), V)),
  (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen a))
    ((Spec (.of A)).presheaf.map (homOfLE ((Spec (.of A)).basicOpen_le a)).op).hom)
variable (hI : Affine.idealCompatible IA I) (hγ : Affine.dividedPowersCompatible IA γA I γS)
variable (hpI : IsNilpotent (Ideal.Quotient.mk IA (p : A)))
variable (F : CrisModuleSheaf (Spec (.of A)) I γS hc (smoothLift f I) (smoothLift_x₀ f I))
variable [CrisModuleSheaf.IsCrystal F] [hqc : CrisModuleSheaf.IsLocallyQuasiCoherent F]

variable (hft : ∀ Aobj, (F.obj Aobj).IsFiniteType)

/- Remark 60.24.14 (Complete comparison): a finite type quasi-coherent crystal on the
closed fibre admits a coherent algebraization with integrable connection, compatible reductions,
and the crystalline–de Rham comparison for those same witnesses. -/
@[stacks 07MZ] #check
  (AlgebraicGeometry.Scheme.Crystalline.Complete.exists_algebraization_comparison
    γA f I γS hc hI hγ hpI F hft :
    ∃ (FY : Y.Modules) (hcoh : FY.IsCoherent)
      (nabla : asBaseSheaf f FY ⟶ asBaseSheaf f (oneFormTensor f FY))
      (hconn : IsConnection f FY nabla) (hnabla : IsIntegrable f FY hcoh nabla hconn)
      (hred : AlgebraicGeometry.Scheme.Crystalline.Complete.ReductionSystem γA f I γS hc hI hγ hpI F FY nabla),
      IsIsomorphic (AlgebraicGeometry.Scheme.Crystalline.Complete.crystallineSections p f I γS hc hI hpI F)
        (deRhamSections f FY hcoh nabla hconn hnabla))
