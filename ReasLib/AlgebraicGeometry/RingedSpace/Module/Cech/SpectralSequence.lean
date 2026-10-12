/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Comparison
public import ReasLib.CategoryTheory.Filtration.Complex.Convergence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cech-to-cohomology spectral sequences for modules

The filtered complex and its spectral sequence are stored as a reusable system.  Page-two and
abutment identifications are explicit fields, while boundedness and convergence remain proof
fields.  No edge morphism is claimed until the filtered-complex API exposes that construction.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleCech

variable {X : RingedSpace.{u}} (U : Opens X.carrier)
variable {ι : Type u} (cover : ι → Over U)
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [HasInjectiveResolutions X.Modules]

/-- A first-quadrant Cech-to-cohomology spectral sequence for one module sheaf, including its
page-two and abutment identifications. -/
@[stacks 01ES "module Cech-to-cohomology spectral sequence system"]
structure SpectralSequenceSystem (F : X.Modules) where
  /-- The filtered complex whose spectral sequence is used. -/
  filteredComplex : FilteredComplex (ModuleCat (sectionsRingOnOpen X U))
  /-- The associated cohomological spectral sequence. -/
  spectralSequence :
    CohomologicalSpectralSequence (ModuleCat (sectionsRingOnOpen X U)) 0
  /-- The spectral sequence is associated to the stored filtered complex. -/
  associated : FilteredComplex.IsAssociated filteredComplex spectralSequence
  /-- The second page is Cech cohomology of the module-valued cohomology presheaves. -/
  pageTwoIso (p q : ℕ) :
    (spectralSequence.page 2).X (Int.ofNat p, Int.ofNat q) ≅
      presheafCohomology U cover
        (((SheafOfModules.forget X.ringCatSheaf).rightDerived q).obj F) p
  /-- The filtered-complex cohomology is ordinary module cohomology on `U`. -/
  abutmentIso (n : ℕ) :
    filteredComplex.underlying.homology (Int.ofNat n) ≅
      moduleCohomologyAtOpen U F n
  /-- The spectral sequence is bounded. -/
  bounded : spectralSequence.IsBounded
  /-- The induced cohomology filtration is finite. -/
  filtrationFinite : FilteredComplex.Cohomology.Filtration.IsFinite filteredComplex
  /-- The spectral sequence converges to the filtered-complex cohomology. -/
  converges : FilteredComplex.Cohomology.Convergence.Converges
    filteredComplex spectralSequence

/-- Lemma 20.11.5 (01ES): a covering family gives a Cech-to-cohomology spectral-sequence system
for every module sheaf. -/
@[stacks 01ES "existence of the module Cech spectral sequence"]
theorem spectralSequenceSystem_nonempty
    (hcover : ((Opens.grothendieckTopology X.carrier).over U).CoversTop cover)
    (F : X.Modules) :
    Nonempty (SpectralSequenceSystem U cover F) := sorry

/-- Open-family form of the Cech-to-cohomology spectral-sequence existence theorem. -/
@[stacks 01ES "module Cech spectral sequence for an indexed open cover"]
theorem spectralSequenceSystem_nonempty_of_iSup_eq
    (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U) (F : X.Modules) :
    Nonempty
      (SpectralSequenceSystem U (Opens.Cover.overFamily U 𝒰 h𝒰) F) := sorry

end AlgebraicGeometry.RingedSpace.ModuleCech
