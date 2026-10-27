/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Sites.Simplicial.AugmentationCartesian
public import ReasLib.CategoryTheory.Sites.Grothendieck.AugmentationCartesian
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.AugmentationCartesian
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.FiberAugmentationCartesian

/-!
# Lemma 85.12.3

Cartesian inverse images along augmentations in both presentations of a simplicial site.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite RingedSite
open scoped CategoryTheory.MorphismOfTopoiIn Simplicial

noncomputable section

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [IsMorphismDiagram.{u, v, max u v} C J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type (max u v))]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type (max u v)),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]

section InverseImage

variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : D ⥤ C.obj ⦋0⦌)
variable [HasWeakSheafify K.toGrothendieck (Type (max u v))]
variable [HasWeakSheafify (topology C J) (Type (max u v))]
variable [∀ P : Dᵒᵖ ⥤ Type (max u v), u0.op.HasLeftKanExtension P]
variable [∀ (n : SimplexCategory) (P : Dᵒᵖ ⥤ Type (max u v)),
    (IsAugmentation.stageFunctor C u0 n).op.HasLeftKanExtension P]
variable [HasEqualizers (Sheaf K.toGrothendieck (Type (max u v)))]
variable [IsAugmentation.{u, v, max u v} C J K u0]

/- Lemma 85.12.3 (1)
Case A: Inverse image of a set-valued sheaf along a simplicial augmentation is cartesian. -/
@[stacks 0D7H]
#check (CategoryTheory.SimplicialSites.inverseImage_isCartesian C J K u0 :
    ∀ (G : Sheaf K.toGrothendieck (Type (max u v))),
      IsCartesian C J ((IsAugmentation.inverseImage.{u, v, max u v} C J K u0).obj G))

section Abelian

variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{max u v}]
variable [∀ (n : SimplexCategory) (P : Dᵒᵖ ⥤ AddCommGrpCat.{max u v}),
    (IsAugmentation.stageFunctor C u0 n).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{max u v}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [HasSheafify K.toGrothendieck AddCommGrpCat.{max u v}]
variable [HasSheafify (topology C J) AddCommGrpCat.{max u v}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{max u v}]

/- Lemma 85.12.3 (2)
Case A: Inverse image of an abelian sheaf along a simplicial augmentation is cartesian. -/
@[stacks 0D7H]
#check (CategoryTheory.SimplicialSites.abelianInverseImage_isCartesian C J K u0 :
    ∀ (G : Sheaf K.toGrothendieck AddCommGrpCat.{max u v}),
      Abelian.IsCartesian C J
      ((IsAugmentation.abelianInverseImage.{u, v, max u v} C J K u0).obj G))

/- Lemma 85.12.3 (3)
Case A: The unbounded derived inverse image along a simplicial augmentation is cartesian. -/
@[stacks 0D7H]
#check (CategoryTheory.SimplicialSites.derivedInverseImage_isCartesian C J K u0 :
    ∀ (dK : DerivedCategory (Sheaf K.toGrothendieck AddCommGrpCat.{max u v})),
      Derived.IsCartesian C J
      ((IsAugmentation.derivedInverseImage.{u, v, max u v} C J K u0).obj dK))

end Abelian

end InverseImage

end CategoryTheory.SimplicialSites

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [IsMorphismDiagram.{u, v, max u v} C J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type (max u v))]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type (max u v)),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]

variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : D ⥤ C.obj ⦋0⦌)
variable [HasWeakSheafify K.toGrothendieck (Type (max u v))]
variable [HasWeakSheafify (topology C J) (Type (max u v))]
variable [∀ P : Dᵒᵖ ⥤ Type (max u v), u0.op.HasLeftKanExtension P]
variable [∀ (n : SimplexCategory) (P : Dᵒᵖ ⥤ Type (max u v)),
    (IsAugmentation.stageFunctor C u0 n).op.HasLeftKanExtension P]
variable [HasEqualizers (Sheaf K.toGrothendieck (Type (max u v)))]
variable [IsAugmentation.{u, v, max u v} C J K u0]

variable (O : Sheaf (topology C J) RingCat.{max u v})
variable (O_D : Sheaf K.toGrothendieck RingCat.{max u v})
variable [(topology C J).HasSheafCompose (forget RingCat.{max u v})]
variable [K.toGrothendieck.HasSheafCompose (forget RingCat.{max u v})]
variable (aSharp : O_D ⟶ (IsAugmentation.totalTopos C J K u0).ringDirectImage.obj O)

variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{max u v})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type (max u v))]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type (max u v),
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{max u v}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{max u v}
      (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ n, ToposHom.HasModulePullbackDerived (stageMorphism C J O n)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (ringedToposMap C J O φ)]
variable [(SheafOfModules.restrictScalars.{max u v}
    (IsAugmentation.ringedTopos C J K u0 O O_D aSharp).structureMap).IsRightAdjoint]

/- Lemma 85.12.3 (4)
Case A: Module pullback along the ringed augmentation is cartesian. -/
@[stacks 0D7H]
#check (CategoryTheory.SimplicialSites.modulePullback_isCartesian C J K u0 O O_D aSharp :
    ∀ (M : SheafOfModules.{max u v} O_D),
      Module.IsCartesian C J O
      ((IsAugmentation.ringedTopos C J K u0 O O_D aSharp).modulePullback.obj M))

variable [ToposHom.HasModulePullbackDerived
  (IsAugmentation.ringedTopos C J K u0 O O_D aSharp)]

/- Lemma 85.12.3 (5)
Case A: Unbounded derived module pullback along the ringed augmentation is cartesian. -/
@[stacks 0D7H]
#check (CategoryTheory.SimplicialSites.modulePullbackDerived_isCartesian C J K u0 O O_D aSharp :
    ∀ (dK : Hom.ModuleDerived.{max u v} (ofRingSheaf K.toGrothendieck O_D)),
      ModuleDerived.IsCartesian C J O
      ((IsAugmentation.ringedTopos C J K u0 O O_D aSharp).modulePullbackDerived.obj dK))

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : F.obj (op ⦋0⦌) ⥤ D)
variable [K.IsSite]
variable [∀ n, (J n).IsSite]
variable [HasWeakSheafify K.toGrothendieck (Type w)]
variable [HasSheafify K.toGrothendieck (Type w)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [∀ (n : SimplexCategory) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    (IsAugmentation.stageFunctor F u0 n).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [HasEqualizers (Sheaf K.toGrothendieck (Type w))]
variable [h_fiberwise : IsFiberwiseSite F J]
variable [h_aug : IsAugmentation F J K u0]

/- Lemma 85.12.3 (6)
Case B: Inverse image of a set-valued sheaf along a fiberwise augmentation is cartesian. -/
@[stacks 0D7H]
#check (CategoryTheory.Grothendieck.inverseImage_isCartesian F J K u0 :
    ∀ (G : Sheaf K.toGrothendieck (Type w)),
      Sheaf.IsCartesian F J (Type w) ((IsAugmentation.inverseImage F J K u0).obj G))

variable [K.toGrothendieck.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
variable [(topology F J).HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]

/- Lemma 85.12.3 (7)
Case B: Canonical abelian inverse image along a fiberwise augmentation is cartesian. -/
@[stacks 0D7H]
#check (CategoryTheory.Grothendieck.abelianInverseImage_isCartesian F J K u0 :
    ∀ (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}),
      Sheaf.IsCartesian F J AddCommGrpCat.{w}
      ((IsAugmentation.totalTopos F J K u0).abelianInverseImage.obj G))

variable [HasSheafify K.toGrothendieck AddCommGrpCat.{w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]

/- Lemma 85.12.3 (8)
Case B: Unbounded derived abelian inverse image along a fiberwise augmentation is cartesian. -/
@[stacks 0D7H]
#check (CategoryTheory.Grothendieck.derivedInverseImage_isCartesian F J K u0 :
    ∀ (dK : DerivedCategory (Sheaf K.toGrothendieck AddCommGrpCat.{w})),
      AbelianDerived.IsCartesian F J ((IsAugmentation.derivedInverseImage F J K u0).obj dK))

end CategoryTheory.Grothendieck

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : F.obj (op ⦋0⦌) ⥤ D)
variable [K.IsSite]
variable [∀ n, (J n).IsSite]
variable [HasWeakSheafify K.toGrothendieck (Type w)]
variable [HasSheafify K.toGrothendieck (Type w)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [∀ (n : SimplexCategory) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    (IsAugmentation.stageFunctor F u0 n).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [HasEqualizers (Sheaf K.toGrothendieck (Type w))]
variable [h_fiberwise : IsFiberwiseSite F J]
variable [h_aug : IsAugmentation F J K u0]

variable (O : Sheaf (topology F J) RingCat.{w})
variable (O_D : Sheaf K.toGrothendieck RingCat.{w})
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [K.toGrothendieck.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable (aSharp : O_D ⟶ (IsAugmentation.totalTopos F J K u0).ringDirectImage.obj O)

variable [UnivLE.{max u v, w}]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [HasSheafify (topology F J) (Type w)]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]

variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (fiberRingedToposMap F J O φ).structureMap).IsRightAdjoint]
variable [∀ n, ToposHom.HasModulePullbackDerived (fiberStageMorphism F J O n)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (fiberRingedToposMap F J O φ)]

variable [(SheafOfModules.restrictScalars.{w}
    (IsAugmentation.ringedTopos F J K u0 O O_D aSharp).structureMap).IsRightAdjoint]

/- Lemma 85.12.3 (9)
Case B: Module pullback along a ringed fiberwise augmentation is cartesian. -/
@[stacks 0D7H]
#check (CategoryTheory.Grothendieck.modulePullback_isCartesian F J K u0 O O_D aSharp :
    ∀ (M : SheafOfModules.{w} O_D),
      Module.IsCartesian F J O
      ((IsAugmentation.ringedTopos F J K u0 O O_D aSharp).modulePullback.obj M))

variable [ToposHom.HasModulePullbackDerived
  (IsAugmentation.ringedTopos F J K u0 O O_D aSharp)]

/- Lemma 85.12.3 (10)
Case B: Unbounded derived module pullback along a ringed fiberwise augmentation is cartesian. -/
@[stacks 0D7H]
#check (CategoryTheory.Grothendieck.modulePullbackDerived_isCartesian F J K u0 O O_D aSharp :
    ∀ (dK : Hom.ModuleDerived.{w} (ofRingSheaf K.toGrothendieck O_D)),
      ModuleDerived.IsCartesian F J O
      ((IsAugmentation.ringedTopos F J K u0 O O_D aSharp).modulePullbackDerived.obj dK))

end CategoryTheory.Grothendieck
