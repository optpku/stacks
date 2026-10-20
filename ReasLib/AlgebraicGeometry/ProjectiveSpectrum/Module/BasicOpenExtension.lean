module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Basis.Extension

/-!
# Extending module sheaves from the basic opens of `Proj`

This file specializes extension from a topological basis to the canonical basic-open basis of a
projective spectrum and transports the result to its canonical structure sheaf.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.Proj

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The canonical basis of standard basic opens of `Proj 𝒜`. -/
def basicOpenBasis : Set ((AlgebraicGeometry.Proj 𝒜).Opens) :=
  Set.range (basicOpen 𝒜)

/-- The canonical structure sheaf of `Proj 𝒜`, restricted to its basic-open basis. -/
noncomputable def basicOpenRingSheaf :
    BasisSiteSheaf RingCat (basicOpenBasis 𝒜) :=
  BasisSiteSheaf.restrict (isBasis_basicOpen 𝒜) (AlgebraicGeometry.Proj 𝒜).ringCatSheaf

/-- Bundled module-sheaf data on the canonical basic-open basis of `Proj 𝒜`. -/
abbrev BasicOpenModule := SheafOfModules.{u} (basicOpenRingSheaf 𝒜)

/-- Extension of the restricted structure sheaf from basic opens is canonically isomorphic to the
structure sheaf of `Proj 𝒜`. -/
noncomputable def basicOpenRingSheafExtensionIso :
    BasisSiteSheaf.extend (basicOpenRingSheaf 𝒜) (isBasis_basicOpen 𝒜) ≅
      (AlgebraicGeometry.Proj 𝒜).ringCatSheaf :=
  BasisSiteSheaf.extendRestrictSheafIso
    (AlgebraicGeometry.Proj 𝒜).ringCatSheaf (isBasis_basicOpen 𝒜)

/-- Extend explicit module-sheaf data on the basic opens to a module over the canonical structure
sheaf of `Proj 𝒜`. -/
noncomputable def extendModuleFromBasicOpens (ℱ : BasicOpenModule 𝒜) :
    (AlgebraicGeometry.Proj 𝒜).Modules :=
  (SheafOfModules.restrictScalars (basicOpenRingSheafExtensionIso 𝒜).inv).obj
    (BasisSiteSheaf.extendModule_of_isBasis
      (isBasis_basicOpen 𝒜) (basicOpenRingSheaf 𝒜) ℱ)

end AlgebraicGeometry.Proj
