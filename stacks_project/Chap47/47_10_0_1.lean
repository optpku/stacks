/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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
  (letI : Fact I.FG := ⟨hI⟩
  (CategoryTheory.DerivedCategory.LocalCohomology.idealToClosedSupport I hI RΓZ hRΓZ :
    ModuleCat.IdealPowerTorsion.derivedTorsion I ⋙
        CohomologyIn.Comparison.functor (ModuleCat.isIdealPowerTorsion I) ⟶ RΓZ)
  )

#check (letI : Fact I.FG := ⟨hI⟩
  (idealTorsionCounit I hI :
    ((ModuleCat.IdealPowerTorsion.derivedTorsion I ⋙
        CohomologyIn.Comparison.functor (ModuleCat.isIdealPowerTorsion I)) ⋙
      IdealPowerTorsion.inclusion I) ⟶ 𝟭 (DerivedCategory (ModuleCat A)))
  )

#check (letI : Fact I.FG := ⟨hI⟩
  (idealToClosedSupport_fac I hI RΓZ hRΓZ :
  Functor.whiskerRight (idealToClosedSupport I hI RΓZ hRΓZ)
      (IdealPowerTorsion.inclusion I) ≫ hRΓZ.counit = idealTorsionCounit I hI)
  )

end CategoryTheory.DerivedCategory.LocalCohomology
