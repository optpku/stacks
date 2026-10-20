/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.BasicOpenExtension
import StacksCheckRecall

@[expose] public section

universe u v

section

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/- Definition 27.8.3 (`01M6`): the homogeneous spectrum of a graded ring, equipped with its
canonical structure sheaf, is the scheme `AlgebraicGeometry.Proj 𝒜`. -/
@[stacks 01M6] #check (AlgebraicGeometry.Proj 𝒜 : AlgebraicGeometry.Scheme)

/- The standard basic open attached to a homogeneous element. -/
#check (AlgebraicGeometry.Proj.basicOpen 𝒜 :
  A → (AlgebraicGeometry.Proj 𝒜).Opens)

/- The standard basic opens form a basis of the homogeneous spectrum. -/
#check (AlgebraicGeometry.Proj.isBasis_basicOpen 𝒜 :
  TopologicalSpace.Opens.IsBasis (Set.range (AlgebraicGeometry.Proj.basicOpen 𝒜)))

/- The canonical structure sheaf on the homogeneous spectrum. -/
#check (AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf 𝒜 :
  TopCat.Sheaf CommRingCat (ProjectiveSpectrum.top 𝒜))

/- The set of standard basic opens used by the extension construction. -/
#check (AlgebraicGeometry.Proj.basicOpenBasis 𝒜 :
  Set ((AlgebraicGeometry.Proj 𝒜).Opens))

/- Restriction of the canonical ring sheaf to the standard basic-open basis. -/
#check (BasisSiteSheaf.restrict
    (AlgebraicGeometry.Proj.isBasis_basicOpen 𝒜)
    (AlgebraicGeometry.Proj 𝒜).ringCatSheaf :
  BasisSiteSheaf RingCat (AlgebraicGeometry.Proj.basicOpenBasis 𝒜))

/- The canonical basic-open ring sheaf. -/
#check (AlgebraicGeometry.Proj.basicOpenRingSheaf 𝒜 :
  BasisSiteSheaf RingCat (AlgebraicGeometry.Proj.basicOpenBasis 𝒜))

/- Extension after restriction recovers the canonical structure sheaf. -/
#check (BasisSiteSheaf.extendRestrictSheafIso
    (AlgebraicGeometry.Proj 𝒜).ringCatSheaf
    (AlgebraicGeometry.Proj.isBasis_basicOpen 𝒜) :
  BasisSiteSheaf.extend (AlgebraicGeometry.Proj.basicOpenRingSheaf 𝒜)
      (AlgebraicGeometry.Proj.isBasis_basicOpen 𝒜) ≅
    (AlgebraicGeometry.Proj 𝒜).ringCatSheaf)

/- Explicit module-sheaf data on the standard basic opens. -/
#check (AlgebraicGeometry.Proj.BasicOpenModule 𝒜 : Type (u + 1))

/- The generic basis extension applied to the canonical basic-open ring sheaf. -/
#check (BasisSiteSheaf.extendModule_of_isBasis
    (AlgebraicGeometry.Proj.isBasis_basicOpen 𝒜)
    (AlgebraicGeometry.Proj.basicOpenRingSheaf 𝒜) :
  AlgebraicGeometry.Proj.BasicOpenModule 𝒜 →
    SheafOfModules (BasisSiteSheaf.extend
      (AlgebraicGeometry.Proj.basicOpenRingSheaf 𝒜)
      (AlgebraicGeometry.Proj.isBasis_basicOpen 𝒜)))

/- The canonical identification of the extended restricted ring sheaf with the structure sheaf. -/
#check (AlgebraicGeometry.Proj.basicOpenRingSheafExtensionIso 𝒜 :
  BasisSiteSheaf.extend (AlgebraicGeometry.Proj.basicOpenRingSheaf 𝒜)
      (AlgebraicGeometry.Proj.isBasis_basicOpen 𝒜) ≅
    (AlgebraicGeometry.Proj 𝒜).ringCatSheaf)

/- Scalar restriction transports an extended module to the canonical structure sheaf. -/
#check (SheafOfModules.restrictScalars
    (AlgebraicGeometry.Proj.basicOpenRingSheafExtensionIso 𝒜).inv :
  CategoryTheory.Functor
    (SheafOfModules (BasisSiteSheaf.extend
      (AlgebraicGeometry.Proj.basicOpenRingSheaf 𝒜)
      (AlgebraicGeometry.Proj.isBasis_basicOpen 𝒜)))
    ((AlgebraicGeometry.Proj 𝒜).Modules))

/- Applying this construction to the basic-open object `~M` gives the associated
`𝒪_{Proj(𝒜)}`-module sheaf on all opens. -/
#check (AlgebraicGeometry.Proj.extendModuleFromBasicOpens 𝒜 :
  AlgebraicGeometry.Proj.BasicOpenModule 𝒜 → (AlgebraicGeometry.Proj 𝒜).Modules)

end
