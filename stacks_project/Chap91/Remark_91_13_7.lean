/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.FirstOrderThickening.AlgebraExtension.Functoriality
import StacksCheckRecall

/-! # Functoriality of square-zero algebra extensions on ringed topoi -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.FirstOrderThickening
open SheafOfModules.RingedSite.FirstOrderThickening.Solution
open scoped DerivedExt RingedSite.ToposHom

noncomputable section

universe u
namespace RingedSite.ToposHom.AlgebraExtension

-- Local instance justification (defeq pin): the checked extension classes and derived transports must use the standard module derived category.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): the commutative-sheaf module spelling must select the same standard localization dictionary.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

variable {B : Type u} [Category.{u} B] {JB : GrothendieckTopology B}
variable [JB.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [JB.HasSheafCompose (forget RingCat.{u})]
variable [JB.HasSheafCompose (forget CommRingCat.{u})]
variable [JB.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify JB CommRingCat.{u}] [JB.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasSheafify JB AddCommGrpCat.{u}] [JB.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {OB : Sheaf JB CommRingCat.{u}}
variable {C : Type u} [Category.{u} C] {JC : GrothendieckTopology C}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [JC.HasSheafCompose (forget RingCat.{u})]
variable [JC.HasSheafCompose (forget CommRingCat.{u})]
variable [JC.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify JC CommRingCat.{u}] [JC.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasSheafify JC AddCommGrpCat.{u}] [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {OC : Sheaf JC CommRingCat.{u}}
variable {D : Type u} [Category.{u} D] {JD : GrothendieckTopology D}
variable [JD.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [JD.HasSheafCompose (forget RingCat.{u})]
variable [JD.HasSheafCompose (forget CommRingCat.{u})]
variable [JD.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify JD CommRingCat.{u}] [JD.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasSheafify JD AddCommGrpCat.{u}] [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {OD : Sheaf JD CommRingCat.{u}}
variable (f : ToposHom (ofCommRingSheaf JC OC) (ofCommRingSheaf JB OB))
variable (g : ToposHom (ofCommRingSheaf JD OD) (ofCommRingSheaf JC OC))
variable [(SheafOfModules.restrictScalars.{u} g.structureMap).IsRightAdjoint]

variable {F : ModuleCat.{u} (ofCommRingSheaf JC OC)}
variable {G : ModuleCat.{u} (ofCommRingSheaf JD OD)}

/- Remark 91.13.7 (1) The coefficient pushout of the inverse-image source extension. -/
@[stacks 0GQ8] #check (RingedSite.ToposHom.AlgebraExtension.pushoutAlong f g :
    ∀ (c : g.modulePullback.obj F ⟶ G) (S : AlgebraExtension f F),
    Solution (𝟙 (g.toTopos.commRingInverseImage.obj (f.toTopos.commRingInverseImage.obj OB)))
      (isSquareZero_id _) (g.toTopos.commRingInverseImage.map (commRingStructureMap f))
      ((restrictionAlong (commRingStructureMap g)).obj G)
      (zeroKernelMap _ ((restrictionAlong (commRingStructureMap g)).obj G)))

/- Remark 91.13.7 (2) The target extension pulled back along the structure map. -/
@[stacks 0GQ8] #check (RingedSite.ToposHom.AlgebraExtension.pullbackAlong f g :
    ∀ (S : AlgebraExtension (g.comp f) G),
    Solution (𝟙 (g.toTopos.commRingInverseImage.obj (f.toTopos.commRingInverseImage.obj OB)))
      (isSquareZero_id _) (g.toTopos.commRingInverseImage.map (commRingStructureMap f))
      ((restrictionAlong (commRingStructureMap g)).obj G)
      (zeroKernelMap _ ((restrictionAlong (commRingStructureMap g)).obj G)))

/- Remark 91.13.7 (3) A compatible lift exists exactly when the two full algebra extensions are isomorphic. -/
@[stacks 0GQ8] #check (RingedSite.ToposHom.AlgebraExtension.exists_fittingMap_iff_isoClass f g :
    ∀ (c : g.modulePullback.obj F ⟶ G)
    (S : AlgebraExtension f F) (T : AlgebraExtension (g.comp f) G),
    (∃ φ : g.toTopos.commRingInverseImage.obj S.middle ⟶ T.middle, Fits f g c S T φ) ↔
      isoClassMk (pushoutAlong f g c S) = isoClassMk (pullbackAlong f g T))

/- Remark 91.13.7 (4) Tensor–Hom adjunction and cotangent inverse image identify the classifying Ext groups. -/
@[stacks 0GQ8] #check (RingedSite.ToposHom.AlgebraExtension.extOneRestrictEquiv f g :
    ∀ (G : ModuleCat.{u} (ofCommRingSheaf JD OD)),
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj
      (SheafOfModules.RingedSite.NaiveCotangent.obj
        (g.toTopos.commRingInverseImage.obj (f.toTopos.commRingInverseImage.obj OB))
        (Under.mk (g.toTopos.commRingInverseImage.map (commRingStructureMap f)))),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj
        ((restrictionAlong (commRingStructureMap g)).obj G))) ≃
    Ext⁽(1 : ℤ)⁾((DerivedPullback.functor g).obj (DerivedCategory.Q.obj NL[f]),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)))

/- Remark 91.13.7 (5) The pushout class is the canonical image of the source class. -/
@[stacks 0GQ8] #check (RingedSite.ToposHom.AlgebraExtension.pushoutAlong_extClass f g :
    ∀ (c : g.modulePullback.obj F ⟶ G) (S : AlgebraExtension f F),
    extOneRestrictEquiv f g G
      (Solution.extensionClass (g.toTopos.commRingInverseImage.map (commRingStructureMap f))
        ((restrictionAlong (commRingStructureMap g)).obj G)
        (isoClassMk (pushoutAlong f g c S))) =
      NaiveCotangent.extOneMap f g c (extClass f S))

/- Remark 91.13.7 (6) The pullback class is the canonical image of the composite extension class. -/
@[stacks 0GQ8] #check (RingedSite.ToposHom.AlgebraExtension.pullbackAlong_extClass f g :
    ∀ (S : AlgebraExtension (g.comp f) G),
    extOneRestrictEquiv f g G
      (Solution.extensionClass (g.toTopos.commRingInverseImage.map (commRingStructureMap f))
        ((restrictionAlong (commRingStructureMap g)).obj G)
        (isoClassMk (pullbackAlong f g S))) =
      NaiveCotangent.extOneComap f g (extClass (g.comp f) S))

end RingedSite.ToposHom.AlgebraExtension
