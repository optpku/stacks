module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- The positive-degree cohomology of a quasi-coherent module vanishes on an affine open. -/
theorem higherCohomology_isZero_on_affineOpen
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) (p : ℕ) (hp : 0 < p) :
    IsZero (((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ).H' p U) := sorry

/-- Affine schemes have vanishing positive-degree cohomology for quasi-coherent modules. -/
theorem higherCohomology_isZero_of_isAffine
    [IsAffine X]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (p : ℕ) (hp : 0 < p) :
    IsZero (((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ).H' p (⊤ : X.Opens)) := by
  simpa using higherCohomology_isZero_on_affineOpen
    ℱ (⊤ : X.Opens) (isAffineOpen_top X) p hp

end AlgebraicGeometry.Scheme
