module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
public import ReasLib.CategoryTheory.Sites.Topos.InternalCommRing
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat

/-!
# Relative flatness of modules on ringed topoi

A module on the source of a ringed-topos morphism is relatively flat when it is flat over
the canonical commutative-ring inverse image of the target structure sheaf.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe uC vC uB vB w

namespace RingedSite.ToposHom

variable {C : Type uC} [Category.{vC} C] {B : Type uB} [Category.{vB} B]
variable {JC : GrothendieckTopology C} {JB : GrothendieckTopology B}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JB.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JC.HasSheafCompose (forget RingCat.{w})]
variable [JB.HasSheafCompose (forget RingCat.{w})]
variable [HasWeakSheafify JC AddCommGrpCat.{w}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O : Sheaf JC CommRingCat.{w}} {O_B : Sheaf JB CommRingCat.{w}}

/-- An `O`-module is flat over the target of a morphism of ringed topoi when its
restriction along the canonical inverse-image structure map is flat over `f⁻¹ O_B`. -/
def IsFlatOver
    (f : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JB O_B))
    (F : ringedSiteModuleCategory.{uC, vC, w, w} JC O) : Prop :=
  SheafOfModules.RingedSite.IsFlat (f.toTopos.commRingInverseImage.obj O_B)
    ((SheafOfModules.restrictScalars
      (f.toTopos.commRingInverseImageForgetRingIso.hom.app O_B ≫ f.structureMap)).obj F)

/-- Relative flatness is flatness after restriction along the canonical comparison from
commutative-ring inverse image followed by the inverse-image structure map. -/
theorem isFlatOver_iff
    (f : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JB O_B))
    (F : ringedSiteModuleCategory.{uC, vC, w, w} JC O) :
    IsFlatOver f F ↔
      SheafOfModules.RingedSite.IsFlat (f.toTopos.commRingInverseImage.obj O_B)
        ((SheafOfModules.restrictScalars
          (f.toTopos.commRingInverseImageForgetRingIso.hom.app O_B ≫ f.structureMap)).obj F) :=
  Iff.rfl

end RingedSite.ToposHom
