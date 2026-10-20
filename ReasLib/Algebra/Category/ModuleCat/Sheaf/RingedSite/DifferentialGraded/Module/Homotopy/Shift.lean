/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.MappingCone.Triangle
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Homotopy

/-!
# Shift compatibility of the underlying homotopy functor

The functor from the DG homotopy category of module sheaves to the ordinary homotopy category
of cochain complexes commutes with integer shifts.  This leaf also compares the image of a DG
mapping-cone triangle with Mathlib's standard mapping-cone triangle in the ordinary homotopy
category.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open ComplexShape
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule.Homotopy

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

-- Local declaration justification (parser conflict): this alias is confined to the underlying
-- cochain shift construction and adds neither a mathematical choice nor public syntax.
local notation "ModO" => ringedSiteModuleCategory J 𝒪

/-- The componentwise shift comparison for the underlying-homotopy functor. -/
noncomputable def shiftIsoApp (𝒜 : DGA(𝒪))
    (X : K ℤ Mod(𝒜, d)) (k : ℤ) :
    (CategoryTheory.shiftFunctor (K ℤ Mod(𝒜, d)) k ⋙ forget 𝒜).obj X ≅
      (forget 𝒜 ⋙
        CategoryTheory.shiftFunctor (HomotopyCategory ModO (up ℤ)) k).obj X :=
  (HomotopyCategory.quotient ModO (up ℤ)).mapIso
      ((Shift.forgetIso 𝒜 k).app X.obj) ≪≫
    ((HomotopyCategory.quotient ModO (up ℤ)).commShiftIso k).app
      X.obj.toComplex

/-- The underlying-homotopy functor identifies the shifted DG module with the shift of its
underlying cochain complex. -/
noncomputable def shiftIso (𝒜 : DGA(𝒪)) (k : ℤ) :
    CategoryTheory.shiftFunctor (K ℤ Mod(𝒜, d)) k ⋙ forget 𝒜 ≅
      forget 𝒜 ⋙
        CategoryTheory.shiftFunctor (HomotopyCategory ModO (up ℤ)) k :=
  NatIso.ofComponents (fun X ↦ shiftIsoApp 𝒜 X k) (fun _ ↦ sorry)

/-- The shift comparison is the composite of the underlying-complex comparison and Mathlib's
homotopy-quotient shift comparison. -/
theorem shiftIso_app_eq (𝒜 : DGA(𝒪))
    (X : K ℤ Mod(𝒜, d)) (k : ℤ) :
    (shiftIso 𝒜 k).app X =
      (HomotopyCategory.quotient ModO (up ℤ)).mapIso
          ((Shift.forgetIso 𝒜 k).app X.obj) ≪≫
        ((HomotopyCategory.quotient ModO (up ℤ)).commShiftIso k).app
          X.obj.toComplex := sorry

/-- Forgetting the DG action on homotopy categories commutes with integer shifts. -/
noncomputable instance forgetCommShift (𝒜 : DGA(𝒪)) :
    (forget 𝒜).CommShift ℤ where
  commShiftIso k := shiftIso 𝒜 k
  commShiftIso_zero := sorry
  commShiftIso_add := sorry

section MappingCone

variable [HasBinaryBiproducts (ringedSiteModuleCategory J 𝒪)]
variable {𝒜 : DGA(𝒪)} {X Y : Mod(𝒜, d)}

/-- After forgetting the DG action, the DG mapping-cone triangle is canonically isomorphic to
Mathlib's standard mapping-cone triangle in the ordinary homotopy category. -/
noncomputable def mappingConeTriangleIso (f : X ⟶ Y) :
    (forget 𝒜).mapTriangle.obj (MappingCone.triangleK f) ≅
      CochainComplex.mappingCone.triangleh f.toCochainMap :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    ((HomotopyCategory.quotient ModO (up ℤ)).mapIso
      (_root_.SheafOfModules.RingedSite.DifferentialGradedModule.mappingConeToCochainMappingCone
        f))
    sorry sorry sorry

end MappingCone

end


end SheafOfModules.RingedSite.DifferentialGradedModule.Homotopy
