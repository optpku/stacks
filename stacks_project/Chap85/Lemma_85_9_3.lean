/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Sites.Simplicial.AugmentationSpectralSequence
public import ReasLib.CategoryTheory.Sites.Grothendieck.AugmentationSpectralSequence
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck

/-!
# Augmentation spectral sequences

The augmentation spectral sequence has first page `R^q a_{p,*} K_p`, the canonical
Čech differential, and abutment `R^{p+q} a_* K`, functorially in `K`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex ComplexShape DerivedCategory Opposite
open FilteredComplex.SpectralSequence.Realization
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : D ⥤ C.obj ⦋0⦌)
variable [HasWeakSheafify K.toGrothendieck (Type (max u v))]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type (max u v))]
variable [HasWeakSheafify (topology C J) (Type (max u v))]
variable [∀ P : Dᵒᵖ ⥤ Type (max u v), u0.op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type (max u v)),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [h_morphism : IsMorphismDiagram C J]
variable [h_aug : IsAugmentation C J K u0]
variable [∀ (n : SimplexCategory) (P : Dᵒᵖ ⥤ Type (max u v)),
    (IsAugmentation.stageFunctor C u0 n).op.HasLeftKanExtension P]
variable [∀ n, (ofStage C n).IsContinuous (J n).toGrothendieck (topology C J)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type (max u v), (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{max u v}]
variable [∀ (n : SimplexCategory) (P : Dᵒᵖ ⥤ AddCommGrpCat.{max u v}),
    (IsAugmentation.stageFunctor C u0 n).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{max u v}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{max u v}]
variable [HasSheafify (topology C J) AddCommGrpCat.{max u v}]
variable [HasSheafify K.toGrothendieck AddCommGrpCat.{max u v}]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{max u v},
    (ofStage C n).op.HasLeftKanExtension P]
variable [HasEqualizers (Sheaf K.toGrothendieck AddCommGrpCat.{max u v})]

/- Lemma 85.9.3 (1): Existence of the augmentation spectral sequence
for morphism diagrams of sites. -/
@[stacks 0D7A] #check (CategoryTheory.SimplicialSites.exists_augmentationSpectralSequence C J K u0 :
    ∀ X : DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{max u v}),
    ∃ (S : WithAbutment (fun n ↦ augmentationAbutmentFunctor C J K u0 n) X)
      (pageOneIso : ∀ p q : ℤ,
        (S.sequence.page 1).X (p, q) ≅
          (augmentationPageOneFunctor C J K u0 p q).obj X),
      ∀ p q : ℤ,
        (pageOneIso p q).hom ≫ (augmentationPageOneDifferential C J K u0 p q).app X =
          (S.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIso (p + 1) q).hom)

/- Lemma 85.9.3 (2): Functoriality of the augmentation spectral sequence
for morphism diagrams of sites. -/
@[stacks 0D7A] #check (CategoryTheory.SimplicialSites.augmentationSpectralSequence_functorial C J K u0 :
    ∃ (S : ∀ X : DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{max u v}),
        WithAbutment (fun n ↦ augmentationAbutmentFunctor C J K u0 n) X)
      (pageOneIso : ∀ (X : DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{max u v})) (p q : ℤ),
        ((S X).sequence.page 1).X (p, q) ≅
          (augmentationPageOneFunctor C J K u0 p q).obj X)
      (m : ∀ {X Y : DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{max u v})} (f : X ⟶ Y),
        WithAbutment.Map (fun n ↦ augmentationAbutmentFunctor C J K u0 n) f (S X) (S Y)),
      (∀ (X : DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{max u v})) (p q : ℤ),
        (pageOneIso X p q).hom ≫ (augmentationPageOneDifferential C J K u0 p q).app X =
          ((S X).sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIso X (p + 1) q).hom) ∧
      (∀ {X Y : DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{max u v})} (f : X ⟶ Y) (p q : ℤ),
        ((m f).sequenceMap.hom 1).f (p, q) ≫ (pageOneIso Y p q).hom =
          (pageOneIso X p q).hom ≫ (augmentationPageOneFunctor C J K u0 p q).map f) ∧
      (∀ X : DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{max u v}),
        (m (𝟙 X)).sequenceMap = 𝟙 (S X).sequence) ∧
      (∀ {X Y Z : DerivedCategory.Plus (Sheaf (topology C J) AddCommGrpCat.{max u v})} (f : X ⟶ Y) (g : Y ⟶ Z),
        (m (f ≫ g)).sequenceMap = (m f).sequenceMap ≫ (m g).sequenceMap))

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : F.obj (op ⦋0⦌) ⥤ D)
variable [IsFiberwiseSite F J]
variable [IsAugmentation F J K u0]
variable [∀ n, (ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{max u v}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{max u v}]
variable [HasSheafify (topology F J) AddCommGrpCat.{max u v}]
variable [HasSheafify K.toGrothendieck AddCommGrpCat.{max u v}]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{max u v},
    (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (n : SimplexCategory) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{max u v}),
    (IsAugmentation.stageFunctor F u0 n).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{max u v}),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [HasEqualizers (Sheaf K.toGrothendieck AddCommGrpCat.{max u v})]

/- Lemma 85.9.3 (3): Existence of the augmentation spectral sequence
for fiberwise simplicial sites. -/
@[stacks 0D7A] #check (CategoryTheory.Grothendieck.exists_fiberAugmentationSpectralSequence F J K u0 :
    ∀ X : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{max u v}),
    ∃ (S : WithAbutment (fun n ↦ fiberAugmentationAbutmentFunctor F J K u0 n) X)
      (pageOneIso : ∀ p q : ℤ,
        (S.sequence.page 1).X (p, q) ≅
          (fiberAugmentationPageOneFunctor F J K u0 p q).obj X),
      ∀ p q : ℤ,
        (pageOneIso p q).hom ≫
            (fiberAugmentationPageOneDifferential F J K u0 p q).app X =
          (S.sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIso (p + 1) q).hom)

/- Lemma 85.9.3 (4): Functoriality of the augmentation spectral sequence
for fiberwise simplicial sites. -/
@[stacks 0D7A] #check (CategoryTheory.Grothendieck.fiberAugmentationSpectralSequence_functorial F J K u0 :
    ∃ (S : ∀ X : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{max u v}),
        WithAbutment (fun n ↦ fiberAugmentationAbutmentFunctor F J K u0 n) X)
      (pageOneIso : ∀ (X : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{max u v})) (p q : ℤ),
        ((S X).sequence.page 1).X (p, q) ≅
          (fiberAugmentationPageOneFunctor F J K u0 p q).obj X)
      (m : ∀ {X Y : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{max u v})} (f : X ⟶ Y),
        WithAbutment.Map (fun n ↦ fiberAugmentationAbutmentFunctor F J K u0 n) f (S X) (S Y)),
      (∀ (X : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{max u v})) (p q : ℤ),
        (pageOneIso X p q).hom ≫ (fiberAugmentationPageOneDifferential F J K u0 p q).app X =
          ((S X).sequence.page 1).d (p, q) (p + 1, q) ≫
            (pageOneIso X (p + 1) q).hom) ∧
      (∀ {X Y : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{max u v})} (f : X ⟶ Y) (p q : ℤ),
        ((m f).sequenceMap.hom 1).f (p, q) ≫ (pageOneIso Y p q).hom =
          (pageOneIso X p q).hom ≫ (fiberAugmentationPageOneFunctor F J K u0 p q).map f) ∧
      (∀ X : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{max u v}),
        (m (𝟙 X)).sequenceMap = 𝟙 (S X).sequence) ∧
      (∀ {X Y Z : DerivedCategory.Plus (Sheaf (topology F J) AddCommGrpCat.{max u v})} (f : X ⟶ Y) (g : Y ⟶ Z),
        (m (f ≫ g)).sequenceMap = (m f).sequenceMap ≫ (m g).sequenceMap))

end CategoryTheory.Grothendieck
