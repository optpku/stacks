/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Tensor.Bilinear

/-! # Degree-zero cup products for modules on commutative ringed topoi -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite (ringSheaf ringedSiteModuleCategory
  tensorSection tensorSectionUnderlying moduleSheafificationHomEquiv)

noncomputable section

universe uX vX uY vY w

namespace RingedSite.ToposHom.ModulePushforward

variable {C_X : Type uX} [Category.{vX} C_X]
variable {C_Y : Type uY} [Category.{vY} C_Y]
variable {J_X : GrothendieckTopology C_X} {J_Y : GrothendieckTopology C_Y}
variable [J_X.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J_Y.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [J_X.HasSheafCompose (forget RingCat.{w})]
variable [J_Y.HasSheafCompose (forget RingCat.{w})]
variable [HasWeakSheafify J_X AddCommGrpCat.{w}]
variable [J_X.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify J_Y AddCommGrpCat.{w}]
variable [J_Y.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O_X : Sheaf J_X CommRingCat.{w}} {O_Y : Sheaf J_Y CommRingCat.{w}}
variable (f : ToposHom (ofCommRingSheaf J_X O_X) (ofCommRingSheaf J_Y O_Y))

/-- The underlying sheaf pairing for direct image is the product comparison of the right
adjoint followed by direct image of the pure-tensor pairing. -/
def naiveCupProductUnderlying
    (F G : ringedSiteModuleCategory.{uX, vX, w, w} J_X O_X) :
    (Sheaf.InternalModule.ToInternal.underlying (ringSheaf J_Y O_Y)).obj
        (f.modulePushforward.obj F) ⊗
      (Sheaf.InternalModule.ToInternal.underlying (ringSheaf J_Y O_Y)).obj
        (f.modulePushforward.obj G) ⟶
      (Sheaf.InternalModule.ToInternal.underlying (ringSheaf J_Y O_Y)).obj
        (f.modulePushforward.obj (F ⊗ G)) :=
  ((forgetIso f).hom.app F ⊗ₘ (forgetIso f).hom.app G) ≫
    (@Adjunction.rightAdjointLaxMonoidal _ _ _ _ _ _ _ _ f.toTopos.adjunction
      (Functor.OplaxMonoidal.ofChosenFiniteProducts f.toTopos.inverseImage)).μ
      ((Sheaf.InternalModule.ToInternal.underlying (ringSheaf J_X O_X)).obj F)
      ((Sheaf.InternalModule.ToInternal.underlying (ringSheaf J_X O_X)).obj G) ≫
    f.toTopos.pushforward.map (tensorSectionUnderlying O_X F G) ≫
    (forgetIso f).inv.app (F ⊗ G)

/-- The underlying direct-image pairing is linear in each input and commutes with
restriction to every object of the target site. -/
theorem naiveCupProductBilinear_laws
    (F G : ringedSiteModuleCategory.{uX, vX, w, w} J_X O_X) :
    let c : ∀ U : C_Yᵒᵖ, (f.modulePushforward.obj F).val.obj U →
        (f.modulePushforward.obj G).val.obj U →
        (f.modulePushforward.obj (F ⊗ G)).val.obj U :=
      fun U x y ↦ (naiveCupProductUnderlying f F G).hom.app U (x, y)
    (∀ U x x' y, c U (x + x') y = c U x y + c U x' y) ∧
    (∀ U (r : O_Y.obj.obj U) x y, c U (r • x) y = r • c U x y) ∧
    (∀ U x y y', c U x (y + y') = c U x y + c U x y') ∧
    (∀ U (r : O_Y.obj.obj U) x y, c U x (r • y) = r • c U x y) ∧
    (∀ {U V : C_Yᵒᵖ} (i : U ⟶ V) x y,
      (f.modulePushforward.obj (F ⊗ G)).val.map i (c U x y) =
        c V ((f.modulePushforward.obj F).val.map i x)
          ((f.modulePushforward.obj G).val.map i y)) := sorry

/-- The compatible bilinear pairing of module sections underlying the degree-zero cup
product on direct images. -/
def naiveCupProductBilinear
    (F G : ringedSiteModuleCategory.{uX, vX, w, w} J_X O_X) :
    PresheafOfModules.BilinearMap O_Y.obj
      (f.modulePushforward.obj F).val (f.modulePushforward.obj G).val
      (f.modulePushforward.obj (F ⊗ G)).val where
  app U := LinearMap.mk₂ (O_Y.obj.obj U)
    (fun x y ↦ (naiveCupProductUnderlying f F G).hom.app U (x, y))
    ((naiveCupProductBilinear_laws f F G).1 U)
    ((naiveCupProductBilinear_laws f F G).2.1 U)
    ((naiveCupProductBilinear_laws f F G).2.2.1 U)
    ((naiveCupProductBilinear_laws f F G).2.2.2.1 U)
  naturality := (naiveCupProductBilinear_laws f F G).2.2.2.2

/-- The degree-zero cup product from the tensor of two module direct images to the direct
image of their tensor product. -/
def naiveCupProduct
    (F G : ringedSiteModuleCategory.{uX, vX, w, w} J_X O_X) :
    f.modulePushforward.obj F ⊗ f.modulePushforward.obj G ⟶
      f.modulePushforward.obj (F ⊗ G) :=
  (SheafOfModules.RingedSite.ModuleSheafification.tensorObjIso O_Y
      (f.modulePushforward.obj F) (f.modulePushforward.obj G)).hom ≫
    (moduleSheafificationHomEquiv O_Y
      (PresheafOfModules.Monoidal.tensorObj
        (f.modulePushforward.obj F).val (f.modulePushforward.obj G).val)
      (f.modulePushforward.obj (F ⊗ G))).symm
        (PresheafOfModules.BilinearMap.toHom (naiveCupProductBilinear f F G))

/-- The cup product is the descent of its sectionwise bilinear pairing along the
sheafification of the pointwise tensor product. -/
theorem naiveCupProduct_eq
    (F G : ringedSiteModuleCategory.{uX, vX, w, w} J_X O_X) :
    naiveCupProduct f F G =
      (SheafOfModules.RingedSite.ModuleSheafification.tensorObjIso O_Y
        (f.modulePushforward.obj F) (f.modulePushforward.obj G)).hom ≫
      (moduleSheafificationHomEquiv O_Y
        (PresheafOfModules.Monoidal.tensorObj
          (f.modulePushforward.obj F).val (f.modulePushforward.obj G).val)
        (f.modulePushforward.obj (F ⊗ G))).symm
          (PresheafOfModules.BilinearMap.toHom (naiveCupProductBilinear f F G)) := rfl

/-- On a pure tensor of sections, the cup product agrees with the underlying direct-image
pairing. -/
theorem naiveCupProduct_tensorSection
    (F G : ringedSiteModuleCategory.{uX, vX, w, w} J_X O_X) (U : C_Yᵒᵖ)
    (x : (f.modulePushforward.obj F).val.obj U)
    (y : (f.modulePushforward.obj G).val.obj U) :
    (naiveCupProduct f F G).val.app U (tensorSection O_Y U x y) =
      (naiveCupProductUnderlying f F G).hom.app U (x, y) := sorry

/-- The degree-zero cup product is natural simultaneously in both module arguments. -/
theorem naiveCupProduct_natural
    {F F' G G' : ringedSiteModuleCategory.{uX, vX, w, w} J_X O_X}
    (α : F ⟶ F') (β : G ⟶ G') :
    tensorHom (f.modulePushforward.map α) (f.modulePushforward.map β) ≫
        naiveCupProduct f F' G' =
      naiveCupProduct f F G ≫ f.modulePushforward.map (tensorHom α β) := sorry

end RingedSite.ToposHom.ModulePushforward
