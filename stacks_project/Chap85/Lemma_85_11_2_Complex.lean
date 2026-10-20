module

public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.ModuleResolution
public import ReasLib.CategoryTheory.Sites.Grothendieck.SimplicialTopos

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor RingedSite
open scoped Simplicial

noncomputable section

universe u v w uD vD

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
variable [(topology C J).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w} (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {D : RingedSite.{uD, vD, w}}
variable [D.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [D.siteTopology.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable (a : ToposHom (totalRingedSite C J O) D)
variable [(SheafOfModules.restrictScalars.{w} a.structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    ((stageMorphism C J O n).comp a).structureMap).IsRightAdjoint]
variable (G : SheafOfModules.{w} D.structureSheaf)

/-- Module pushforward along a stage inclusion followed by a ringed morphism is
pushforward along their composite. -/
def stageModulePushforwardCompIso (n : SimplexCategory) :
    (stageMorphism C J O n).modulePushforward ⋙ a.modulePushforward ≅
      ((stageMorphism C J O n).comp a).modulePushforward :=
  ToposHom.modulePushforwardCompIso (stageMorphism C J O n) a

#check (CategoryTheory.SimplicialSites.stageModulePushforwardCompIso C J O a :
  ∀ n : SimplexCategory,
    (stageMorphism C J O n).modulePushforward ⋙ a.modulePushforward ≅
      ((stageMorphism C J O n).comp a).modulePushforward)

end CategoryTheory.SimplicialSites
