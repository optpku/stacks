module

public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.ModuleCech
public import ReasLib.CategoryTheory.Sites.Grothendieck.SimplicialTopos

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex RingedSite
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable [UnivLE.{max u v, w}]

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : D ⥤ C.obj ⦋0⦌)
variable [HasWeakSheafify K.toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ P : Dᵒᵖ ⥤ Type w, u0.op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [h_morphism : IsMorphismDiagram C J]
variable [h_aug : IsAugmentation C J K u0]
variable [∀ (n : SimplexCategory) (P : Dᵒᵖ ⥤ Type w),
    (IsAugmentation.stageFunctor C u0 n).op.HasLeftKanExtension P]
variable [HasEqualizers (Sheaf K.toGrothendieck (Type w))]
variable (O : Sheaf (topology C J) RingCat.{w})
variable (O_D : Sheaf K.toGrothendieck RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [K.toGrothendieck.HasSheafCompose (forget RingCat.{w})]
variable [(topology C J).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [K.toGrothendieck.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w} (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasWeakSheafify K.toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasSheafify K.toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [(topology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [K.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (aSharp : O_D ⟶
    (IsAugmentation.totalTopos C J K u0).ringDirectImage.obj O)
include h_morphism
include h_aug

/-- The target ringed site presented by the augmentation structure sheaf. -/
abbrev augmentationRingedSite : RingedSite.{u, v, w} :=
  RingedSite.ofRingSheaf K.toGrothendieck O_D

/-- The ringed morphism induced by the augmentation and its structure-sheaf map. -/
abbrev moduleAugmentationHom :
    ToposHom (totalRingedSite C J O)
      (ofRingSheaf K.toGrothendieck O_D) :=
  IsAugmentation.ringedHom C J K u0 O O_D aSharp

omit [UnivLE.{max u v, w}] in
theorem moduleAugmentationHom_toTopos :
    (moduleAugmentationHom C J K u0 O O_D aSharp).toTopos =
      IsAugmentation.totalTopos C J K u0 :=
  IsAugmentation.ringedHom_toTopos C J K u0 O O_D aSharp

variable [(SheafOfModules.restrictScalars.{w}
    (IsAugmentation.ringedHom C J K u0 O O_D aSharp).structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    ((stageMorphism C J O n).comp
      (IsAugmentation.ringedHom C J K u0 O O_D aSharp)).structureMap).IsRightAdjoint]
variable (F : SheafOfModules.{w} O)

#check (CategoryTheory.SimplicialSites.modulePushforwardCosimplicial C J K u0 O O_D aSharp F :
  CosimplicialObject (SheafOfModules.{w} O_D))

#check (CategoryTheory.SimplicialSites.moduleAugmentationCechCochain C J K u0 O O_D aSharp F :
  CochainComplex (SheafOfModules.{w} O_D) ℤ)

#check (CategoryTheory.SimplicialSites.homModuleAugmentationCechCochain C J K u0 O O_D aSharp F :
  SheafOfModules.{w} O_D → CochainComplex AddCommGrpCat ℤ)

end CategoryTheory.SimplicialSites
