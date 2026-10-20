module

public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.LowerShriek
public import stacks_project.Chap85.Lemma_85_6_1_Ringed

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor
open RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable [UnivLE.{max u v, w}]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [HasWeakSheafify (topology C J) (Type w)]

#check (CategoryTheory.SimplicialSites.moduleLowerShriek.adjunction C J O :
  ∀ n, moduleLowerShriek C J O n ⊣ Cocontinuous.moduleInverseImage (ofStage C n) O)

#check (CategoryTheory.SimplicialSites.moduleInverseImageIsoModulePullback C J O :
  ∀ n, Cocontinuous.moduleInverseImage (ofStage C n) O ≅
    (stageMorphism C J O n).modulePullback)

#check (CategoryTheory.SimplicialSites.stageMorphism_modulePullback_isRightAdjoint C J O :
  ∀ n, ((stageMorphism C J O n).modulePullback).IsRightAdjoint)

variable (n : SimplexCategory)

#check ((CategoryTheory.SimplicialSites.moduleLowerShriek.adjunction C J O n).ofNatIsoRight
    (CategoryTheory.SimplicialSites.moduleInverseImageIsoModulePullback C J O n) :
  moduleLowerShriek C J O n ⊣ (stageMorphism C J O n).modulePullback)

#check (CategoryTheory.SimplicialSites.moduleLowerShriek_componentCoproductHom_isIso C J O :
  ∀ (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (SheafOfModules.{w} (componentRingSheaf C J O m))]
    (G : SheafOfModules.{w} (componentRingSheaf C J O n)),
    IsIso (moduleLowerShriek_componentCoproductHom C J O n m G))

end CategoryTheory.SimplicialSites
