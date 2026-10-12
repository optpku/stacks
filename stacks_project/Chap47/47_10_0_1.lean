/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.DerivedTorsion.Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.LocalCohomology

variable {A : Type u} [CommRing A]
variable (I : Ideal A) (hI : I.FG)
variable (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
variable (hRΓZ : IdealPowerTorsion.inclusion I ⊣ RΓZ)

/- 47.10.0.1: for a finitely generated ideal `I` and `Z = V(I)`, the canonical
comparison followed by derived ideal-power torsion maps naturally to closed-support
local cohomology. -/
@[stacks 0A6U] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.idealToClosedSupport I hI RΓZ hRΓZ :
    ModuleCat.IdealPowerTorsion.derivedTorsion I ⋙
        CohomologyIn.Comparison.functor (ModuleCat.isIdealPowerTorsion I) ⟶ RΓZ)

#check (idealTorsionCounit I :
    ((ModuleCat.IdealPowerTorsion.derivedTorsion I ⋙
        CohomologyIn.Comparison.functor (ModuleCat.isIdealPowerTorsion I)) ⋙
      IdealPowerTorsion.inclusion I) ⟶ 𝟭 (DerivedCategory (ModuleCat A)))

#check (idealToClosedSupport_fac I hI RΓZ hRΓZ :
  Functor.whiskerRight (idealToClosedSupport I hI RΓZ hRΓZ)
      (IdealPowerTorsion.inclusion I) ≫ hRΓZ.counit = idealTorsionCounit I)

end CategoryTheory.DerivedCategory.LocalCohomology
