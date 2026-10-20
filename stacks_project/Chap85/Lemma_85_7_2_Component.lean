module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import ReasLib.CategoryTheory.Sites.Topos.ModuleAdjunction
public import stacks_project.Chap85.Lemma_85_5_2_Total
public import stacks_project.Chap85.Lemma_85_6_1_LowerShriek
public import stacks_project.Chap85.Remark_85_7_1_Morphism

public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Morphism

/-!
# Component ringed morphism compatibility checks
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
Canonical shared mathematical interface. -/
#check (CategoryTheory.SimplicialSites.RingedMorphism.topos f :
    ∀ (n : SimplexCategory),
    ToposHom (componentRingedSite C J O n) (componentRingedSite C' J' O' n))

#check (CategoryTheory.SimplicialSites.RingedMorphism.inverseImage_comp f :
    ∀ (n : SimplexCategory),
    (IsMorphism.total J J' f.toSimplicial).ringInverseImage ⋙
        (ofStageMorphism C J n).ringInverseImage ≅
      (ofStageMorphism C' J' n).ringInverseImage ⋙
        (IsMorphism.topos J J' f.toSimplicial n).ringInverseImage)

#check (CategoryTheory.SimplicialSites.RingedMorphism.inverseImage_comp_structureMap f :
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

#check (CategoryTheory.SimplicialSites.RingedMorphism.restrict_modulePushforward f :
    ∀ (n : SimplexCategory),
    (toToposHom f).modulePushforward ⋙ (stageMorphism C' J' O' n).modulePullback ≅
      (stageMorphism C J O n).modulePullback ⋙ (topos f n).modulePushforward)

end RingedMorphism

end CategoryTheory.SimplicialSites
