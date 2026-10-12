/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Torsion

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace CategoryTheory.DerivedCategory

/- This compatibility bridge re-exports the full subcategory of derived modules with
ideal-power-torsion cohomology. -/
#check (@IdealPowerTorsion.{u, v} :
  {A : Type u} → [CommRing A] → Ideal A →
    Type (max (max (v + 1) u) v))

/- This compatibility bridge re-exports the inclusion of the ideal-power-torsion
derived subcategory. -/
#check (@IdealPowerTorsion.inclusion.{u, v} :
  {A : Type u} → [CommRing A] → (I : Ideal A) →
    IdealPowerTorsion.{u, v} I ⥤ DerivedCategory (ModuleCat.{v} A))

variable {A : Type u} [CommRing A]
variable (I : Ideal A) (K : DerivedCategory (ModuleCat.{v} A))

/- Membership in the ideal-power-torsion derived subcategory is the corresponding
degreewise cohomology condition. -/
#check (CohomologyIn.mem_iff (ModuleCat.isIdealPowerTorsion I) K :
  cohomologyIn (ModuleCat.isIdealPowerTorsion I) K ↔
    ∀ n : ℤ, Module.IsIdealPowerTorsion I
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) n).obj K))

variable (X : IdealPowerTorsion.{u, v} I)

/- The generic full-subcategory inclusion leaves the underlying derived object unchanged. -/
#check (ObjectProperty.ι_obj
    (P := cohomologyIn (ModuleCat.isIdealPowerTorsion I)) (X := X) :
  (IdealPowerTorsion.inclusion I).obj X = X.obj)

end CategoryTheory.DerivedCategory
