/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.UniverseLift
public import stacks_project.Chap96.Definition_96_11_1_QCoh
public import stacks_project.Chap96.Lemma_96_19_9
public import stacks_project.Chap96.Proposition_96_20_1

/-!
# Cohomology of a quasi-coherent module via an fppf Čech nerve

A surjective flat 1-morphism of algebraic stacks that is representable by
algebraic spaces and locally of finite presentation computes fppf cohomology
of a quasi-coherent module from the relative Čech nerve.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Bicategory Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {U X : GroupoidsOver S}

/-- The Čech-cohomology universe of an `𝒪_𝒳`-module on the associated fppf site. -/
noncomputable abbrev associatedFppfModuleCarrierLift
    (F : SheafOfModules.{u} (associatedStructureSheaf X StandardTopology.fppf)) :
    SheafOfModules.{u + 1} (associatedStructureSheaf X StandardTopology.fppf) :=
  RingedSite.Module.carrierLift (associatedRingedSite X StandardTopology.fppf) F

/-- `associatedFppfModuleCarrierLift` is the canonical ringed-site carrier lift. -/
theorem associatedFppfModuleCarrierLift_eq
    (F : SheafOfModules.{u} (associatedStructureSheaf X StandardTopology.fppf)) :
    associatedFppfModuleCarrierLift F =
      RingedSite.Module.carrierLift (associatedRingedSite X StandardTopology.fppf) F :=
  sorry

/-- Proposition 103.11.6: Let `f : 𝒰 ⟶ 𝒳` be a morphism of algebraic stacks.
Assume `f` is representable by algebraic spaces, surjective, flat, and locally
of finite presentation. Let `F` be a quasi-coherent `𝒪_𝒳`-module. Then there
is a spectral sequence `E₂^{p, q} = H^q(𝒰_p, f_p^* F) ⇒ H^{p+q}(𝒳, F)`,
where `f_p` is the Čech-nerve projection `Cech.proj f ⦋p⦌ : 𝒰 ×_𝒳 ⋯ ×_𝒳 𝒰 ⟶ 𝒳`
on `p+1` factors. The displayed page is the project's page-1 object
`relativeCechModulePageOne f StandardTopology.fppf (associatedFppfModuleCarrierLift F) p q`. -/
@[stacks 0784]
theorem exists_qcohRelativeCechSpectralSequence [AlgebraicStack U]
    [AlgebraicStack X] (f : U ⟶ X)
    (F : SheafOfModules.{u} (associatedStructureSheaf X StandardTopology.fppf))
    [F.IsQuasicoherent] [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
    [Groupoids.Hom.LocallyOfFinitePresentation f]
    [HasSheafify (X.associatedTopology StandardTopology.fppf) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (X.associatedTopology StandardTopology.fppf) AddCommGrpCat.{u + 1})]
    [∀ p : ℕ, HasSheafify (relativeCechSite f StandardTopology.fppf p)
      AddCommGrpCat.{u + 1}]
    [∀ p : ℕ, HasExt.{u + 1}
      (Sheaf (relativeCechSite f StandardTopology.fppf p) AddCommGrpCat.{u + 1})] :
    ∃ (E : CohomologicalSpectralSequenceNat AddCommGrpCat.{u + 1} 1)
      (pageOneIso : ∀ p q : ℕ,
        (E.page 1 le_rfl).X (p, q) ≅
          relativeCechModulePageOne f StandardTopology.fppf
            (associatedFppfModuleCarrierLift F) p q),
      CohomologicalSpectralSequenceNat.ConvergesTo E
        (fun n ↦ (Sheaf.functorH (X.associatedTopology StandardTopology.fppf) n).obj
          ((SheafOfModules.toSheaf
              (associatedStructureSheaf X StandardTopology.fppf)).obj
            (associatedFppfModuleCarrierLift F))) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
