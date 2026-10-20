/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap85.Lemma_85_7_2_Component
public import stacks_project.Chap85.Lemma_85_7_2_Fiberwise
import StacksCheckRecall

/-!
# Lemma 85.7.2

A morphism of ringed simplicial sites induces total and component ringed-topos
morphisms, compatible structure maps, and a mixed comparison on module sheaves.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite
open scoped MorphismOfTopoiIn

noncomputable section

namespace CategoryTheory.SimplicialSites

variable {C C' : SimplexCategory ⥤ Cat.{v, u}}
variable (J : ∀ n, Precoverage (C.obj n)) (J' : ∀ n, Precoverage (C'.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J' n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C'.obj m)ᵒᵖ ⥤ Type w),
    ((C'.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J] [IsMorphismDiagram C' J']
variable [HasWeakSheafify (topology C J) (Type w)]
variable [HasWeakSheafify (topology C' J') (Type w)]
variable (O : Sheaf (topology C J) RingCat.{w})
variable (O' : Sheaf (topology C' J') RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [(topology C' J').HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J' n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, HasSheafify ((J' n).toGrothendieck) (Type w)]
variable [HasSheafify (topology C J) (Type w)]
variable [HasSheafify (topology C' J') (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (C'.obj n)ᵒᵖ ⥤ Type w, (ofStage C' n).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (C'.obj n)ᵒᵖ ⥤ Type w, (ofStage C' n).op.HasPointwiseRightKanExtension P]

namespace RingedMorphism

variable {J J' O O'}
variable (f : RingedMorphism J J' O O')
variable [∀ n (P : (C'.obj n)ᵒᵖ ⥤ Type w),
    ((f.toSimplicial.app n).toFunctor).op.HasLeftKanExtension P]
variable [∀ P : (totalSite C')ᵒᵖ ⥤ Type w,
    (IsMorphism.totalFunctor f.toSimplicial).op.HasLeftKanExtension P]
/- Lemma 85.7.2
The induced total ringed-topos morphism. -/
@[stacks 0DH0] #check (CategoryTheory.SimplicialSites.RingedMorphism.toToposHom f :
    RingedSite.ToposHom (RingedSite.ofRingSheaf (topology C J) O) (RingedSite.ofRingSheaf (topology C' J') O'))

/- Lemma 85.7.2
The induced component ringed-topos morphisms. -/
@[stacks 0DH0] #check (CategoryTheory.SimplicialSites.RingedMorphism.topos f :
    ∀ (n : SimplexCategory),
    ToposHom (componentRingedSite C J O n) (componentRingedSite C' J' O' n))

/- Lemma 85.7.2
The inverse-image square of ring sheaves. -/
@[stacks 0DH0] #check (CategoryTheory.SimplicialSites.RingedMorphism.inverseImage_comp f :
    ∀ (n : SimplexCategory),
    (IsMorphism.total J J' f.toSimplicial).ringInverseImage ⋙
        (ofStageMorphism C J n).ringInverseImage ≅
      (ofStageMorphism C' J' n).ringInverseImage ⋙
        (IsMorphism.topos J J' f.toSimplicial n).ringInverseImage)

/- Lemma 85.7.2
Compatibility of the square with the structure-sheaf maps. -/
@[stacks 0DH0] #check (CategoryTheory.SimplicialSites.RingedMorphism.inverseImage_comp_structureMap f :
    ∀ (n : SimplexCategory),
    (ofStageMorphism C J n).ringInverseImage.map f.structureMap ≫
        (Cocontinuous.structureMapIso
        (X := componentRingedSite C J O n) (Y := totalRingedSite C J O)
        (ofStage C n) (Iso.refl _)).hom =
      (inverseImage_comp f n).hom.app O' ≫
        (IsMorphism.topos J J' f.toSimplicial n).ringInverseImage.map (Cocontinuous.structureMapIso
        (X := componentRingedSite C' J' O' n) (Y := totalRingedSite C' J' O')
        (ofStage C' n) (Iso.refl _)).hom ≫
        (topos f n).structureMap)

variable [UnivLE.{max u v, w}]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C' J' O' n).structureMap).IsRightAdjoint]



/- Lemma 85.7.2
Restriction of total module direct image agrees with component direct image. -/
@[stacks 0DH0] #check (CategoryTheory.SimplicialSites.RingedMorphism.restrict_modulePushforward f :
    ∀ (n : SimplexCategory),
    (toToposHom f).modulePushforward ⋙ (stageMorphism C' J' O' n).modulePullback ≅
      (stageMorphism C J O n).modulePullback ⋙ (topos f n).modulePushforward)

end RingedMorphism

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable {F F' : SimplicialObject Cat.{v, u}}
variable (J : ∀ n, Precoverage (F.obj n)) (J' : ∀ n, Precoverage (F'.obj n))
variable [IsFiberwiseSite F J] [IsFiberwiseSite F' J']
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasSheafify (J' n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [HasSheafify (topology F' J') (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [HasWeakSheafify (topology F' J') (Type w)]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J' n).toGrothendieck (Type w)]
variable (O : Sheaf (topology F J) RingCat.{w})
variable (O' : Sheaf (topology F' J') RingCat.{w})
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(topology F' J').HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J' n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (F'.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F' (op n)).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F'.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F' (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F'.obj (op n))ᵒᵖ ⥤ Type w),
    ((F'.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

namespace RingedMorphism

variable {J J' O O'}
variable (f : RingedMorphism J J' O O')
variable [∀ n (P : (F.obj n)ᵒᵖ ⥤ Type w),
    ((f.toSimplicial.app n).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
    (Grothendieck.map f.toSimplicial).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    ((f.toSimplicial.app (op n)).toFunctor ⋙ ι F' (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n) ⋙ Grothendieck.map f.toSimplicial).op.HasPointwiseRightKanExtension P]
/- Lemma 85.7.2
The induced total ringed-topos morphism. -/
@[stacks 0DH0] #check (CategoryTheory.Grothendieck.RingedMorphism.toToposHom f :
    RingedSite.ToposHom (RingedSite.ofRingSheaf (topology F J) O) (RingedSite.ofRingSheaf (topology F' J') O'))

/- Lemma 85.7.2
The induced component ringed-topos morphisms. -/
@[stacks 0DH0] #check (CategoryTheory.Grothendieck.RingedMorphism.topos f :
    ∀ (n : SimplexCategory),
    ToposHom (fiberComponentRingedSite F J O n) (fiberComponentRingedSite F' J' O' n))

/- Lemma 85.7.2
The inverse-image square of ring sheaves. -/
@[stacks 0DH0] #check (CategoryTheory.Grothendieck.RingedMorphism.inverseImage_comp f :
    ∀ (n : SimplexCategory),
    (IsFiberwiseMorphism.total J J' f.toSimplicial).ringInverseImage ⋙
        (fiberMorphism F J n).ringInverseImage ≅
      (fiberMorphism F' J' n).ringInverseImage ⋙
        (IsFiberwiseMorphism.topos J J' f.toSimplicial n).ringInverseImage)

/- Lemma 85.7.2
Compatibility of the square with the structure-sheaf maps. -/
@[stacks 0DH0] #check (CategoryTheory.Grothendieck.RingedMorphism.inverseImage_comp_structureMap f :
    ∀ (n : SimplexCategory),
    (fiberMorphism F J n).ringInverseImage.map f.structureMap ≫
        (Cocontinuous.structureMapIso
        (X := fiberComponentRingedSite F J O n) (Y := fiberTotalRingedSite F J O)
        (ι F (op n)) (Iso.refl _)).hom =
      (inverseImage_comp f n).hom.app O' ≫
        (IsFiberwiseMorphism.topos J J' f.toSimplicial n).ringInverseImage.map (Cocontinuous.structureMapIso
        (X := fiberComponentRingedSite F' J' O' n) (Y := fiberTotalRingedSite F' J' O')
        (ι F' (op n)) (Iso.refl _)).hom ≫
        (topos f n).structureMap)

variable [UnivLE.{max u v, w}]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F J O n).structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F' J' O' n).structureMap).IsRightAdjoint]



/- Lemma 85.7.2
Restriction of total module direct image agrees with component direct image. -/
@[stacks 0DH0] #check (CategoryTheory.Grothendieck.RingedMorphism.restrict_modulePushforward f :
    ∀ (n : SimplexCategory),
    (toToposHom f).modulePushforward ⋙ (fiberStageMorphism F' J' O' n).modulePullback ≅
      (fiberStageMorphism F J O n).modulePullback ⋙ (topos f n).modulePushforward)

end RingedMorphism

end CategoryTheory.Grothendieck
