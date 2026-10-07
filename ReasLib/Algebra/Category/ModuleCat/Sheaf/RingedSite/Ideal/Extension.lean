module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Subobject.Limits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal

/-!
# Extension of ideal sheaves

This module defines extension of an ideal subobject along a morphism of
commutative ring sheaves on a fixed site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace SheafOfModules.RingedSite.IdealSheaf

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O O' : Sheaf J CommRingCat.{u}}

/-- The canonical map whose image is the extension of an ideal sheaf along a morphism of
commutative ring sheaves on the same site. -/
noncomputable def extensionMap (I : Subobject (unitModule J O)) (alpha : O ⟶ O') :
    (SheafOfModules.pullback (ringedSiteStructureMap alpha)).obj
        (I : ringedSiteModuleCategory J O) ⟶ unitModule J O' :=
  (SheafOfModules.pullback (ringedSiteStructureMap alpha)).map I.arrow ≫
    SheafOfModules.pullbackObjUnitToUnit (ringedSiteStructureMap alpha)

/-- The extension `I O'` of an ideal sheaf along a morphism `O ⟶ O'`, defined as the image
of the scalar-extended ideal inclusion in the structure module of `O'`. -/
noncomputable def extension (I : Subobject (unitModule J O)) (alpha : O ⟶ O') :
    Subobject (unitModule J O') :=
  imageSubobject (extensionMap I alpha)

/-- The canonical scalar-extended ideal map factors through the extended ideal sheaf. -/
theorem extensionMap_factorization (I : Subobject (unitModule J O)) (alpha : O ⟶ O') :
    factorThruImageSubobject (extensionMap I alpha) ≫ (extension I alpha).arrow =
      extensionMap I alpha := sorry

end SheafOfModules.RingedSite.IdealSheaf
