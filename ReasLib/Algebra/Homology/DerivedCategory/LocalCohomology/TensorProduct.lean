/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Cech

/-!
# Local cohomology and derived tensor products

This module records objectwise compatibility of local cohomology with derived tensor products
and closure of ideal-power-torsion cohomology under derived tensor products.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory.DerivedCategory.LocalCohomology

variable {A : Type u} [CommRing A]

/-- Local cohomology of a derived tensor product is isomorphic to tensoring the first factor
with the local cohomology of the second. -/
theorem tensorObjIsoRight (I : Ideal A) (hI : I.FG)
    (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓ : IdealPowerTorsion.inclusion I ⊣ RΓ)
    (K L : DerivedCategory (ModuleCat A)) :
    Nonempty
      ((RΓ.obj (DerivedTensor.Right.obj K L)).obj ≅
        DerivedTensor.Right.obj K (RΓ.obj L).obj) := sorry

/-- Local cohomology of a derived tensor product is isomorphic to tensoring the local
cohomology of the first factor with the second. -/
theorem tensorObjIsoLeft (I : Ideal A) (hI : I.FG)
    (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓ : IdealPowerTorsion.inclusion I ⊣ RΓ)
    (K L : DerivedCategory (ModuleCat A)) :
    Nonempty
      ((RΓ.obj (DerivedTensor.Right.obj K L)).obj ≅
        DerivedTensor.Right.obj (RΓ.obj K).obj L) := sorry

/-- Applying local cohomology to both factors before taking their derived tensor product
does not change the local cohomology of the product. -/
theorem tensorObjIsoBoth (I : Ideal A) (hI : I.FG)
    (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (hRΓ : IdealPowerTorsion.inclusion I ⊣ RΓ)
    (K L : DerivedCategory (ModuleCat A)) :
    Nonempty
      ((RΓ.obj (DerivedTensor.Right.obj K L)).obj ≅
        DerivedTensor.Right.obj (RΓ.obj K).obj (RΓ.obj L).obj) := sorry

/-- If either factor has ideal-power-torsion cohomology, then their derived tensor product
also has ideal-power-torsion cohomology. -/
theorem tensor_mem (I : Ideal A) (hI : I.FG)
    (K L : DerivedCategory (ModuleCat A))
    (hKL : cohomologyIn (ModuleCat.isIdealPowerTorsion I) K ∨
      cohomologyIn (ModuleCat.isIdealPowerTorsion I) L) :
    cohomologyIn (ModuleCat.isIdealPowerTorsion I)
      (DerivedTensor.Right.obj K L) := sorry

end CategoryTheory.DerivedCategory.LocalCohomology
