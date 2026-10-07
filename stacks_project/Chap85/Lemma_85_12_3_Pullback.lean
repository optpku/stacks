module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import stacks_project.Chap85.Lemma_85_4_2_MorphismDiagram

/-!
# Inverse image of abelian sheaves along an augmentation

The total inverse image `a⁻¹` of an augmentation towards a site `D` on sheaves of
abelian groups, assembled from the stage pullbacks `a_n⁻¹`, together with the
induced functor on `D(D)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Functor
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable (u0 : D ⥤ C.obj ⦋0⦌)
variable [HasWeakSheafify K.toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ P : Dᵒᵖ ⥤ Type w, u0.op.HasLeftKanExtension P]
variable [∀ (n : SimplexCategory) (P : Dᵒᵖ ⥤ Type w),
    (IsAugmentation.stageFunctor C u0 n).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [h_morphism : IsMorphismDiagram C J]
variable [h_aug : IsAugmentation C J K u0]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (n : SimplexCategory) (P : Dᵒᵖ ⥤ AddCommGrpCat.{w}),
    (IsAugmentation.stageFunctor C u0 n).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
include h_morphism
include h_aug

/-- Stage presenting functors of the augmentation are continuous. -/
instance IsAugmentation.stageFunctor_isContinuous (n : SimplexCategory) :
    (IsAugmentation.stageFunctor C u0 n).IsContinuous
      K.toGrothendieck (J n).toGrothendieck :=
  (IsAugmentation.stageFunctor_isExactMorphism C J K u0 n).toIsContinuous

/-- Stage inverse image `a_n⁻¹` of abelian sheaves, i.e. sheaf pullback along the
common composite `u_n`. -/
def IsAugmentation.abelianStageInverseImage (n : SimplexCategory) :
    Sheaf K.toGrothendieck AddCommGrpCat.{w} ⥤
      Sheaf (J n).toGrothendieck AddCommGrpCat.{w} :=
  (IsAugmentation.stageFunctor C u0 n).sheafPullback AddCommGrpCat.{w}
    K.toGrothendieck (J n).toGrothendieck

/-- Inverse-image form of `a_m ∘ f_φ = a_n` on abelian sheaves. -/
def IsAugmentation.abelianStageInverseImage_comp {m n : SimplexCategory} (φ : m ⟶ n) :
    IsAugmentation.abelianStageInverseImage C J K u0 m ⋙
      (C.map φ).toFunctor.sheafPullback AddCommGrpCat.{w}
        (J m).toGrothendieck (J n).toGrothendieck ≅
      IsAugmentation.abelianStageInverseImage C J K u0 n :=
  sheafPullbackComp' K.toGrothendieck ((J m).toGrothendieck) ((J n).toGrothendieck)
    (IsAugmentation.stageFunctor C u0 m) (C.map φ).toFunctor
    (IsAugmentation.stageFunctor_compIso C J K u0 φ)

/-- Pushforward-form transition `a_m⁻¹ G ⟶ (f_φ)_* a_n⁻¹ G` of the abelian inverse-image
system. -/
def IsAugmentation.abelianInverseImageSystemMap
    (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) {m n : SimplexCategory} (φ : m ⟶ n) :
    (IsAugmentation.abelianStageInverseImage C J K u0 m).obj G ⟶
      ((C.map φ).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{w}
        (J m).toGrothendieck (J n).toGrothendieck).obj
        ((IsAugmentation.abelianStageInverseImage C J K u0 n).obj G) :=
  (((C.map φ).toFunctor.sheafAdjunctionContinuous AddCommGrpCat.{w}
      (J m).toGrothendieck (J n).toGrothendieck).homEquiv
    ((IsAugmentation.abelianStageInverseImage C J K u0 m).obj G)
    ((IsAugmentation.abelianStageInverseImage C J K u0 n).obj G))
    ((IsAugmentation.abelianStageInverseImage_comp C J K u0 φ).hom.app G)

/-- Restriction of the assembled abelian inverse image along a total-category morphism
`(φ, g) : U ⟶ V`. -/
def IsAugmentation.abelianInverseImagePresheafMap
    (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) {U V : totalSite C} (η : U ⟶ V) :
    ((IsAugmentation.abelianStageInverseImage C J K u0 (degree V)).obj G).obj.obj
      (op (obj V)) ⟶
    ((IsAugmentation.abelianStageInverseImage C J K u0 (degree U)).obj G).obj.obj
      (op (obj U)) :=
  (IsAugmentation.abelianInverseImageSystemMap C J K u0 G (homToPair η).1).hom.app
      (op (obj V)) ≫
    (sheafPushforwardContinuousObjObjIso (C.map (homToPair η).1).toFunctor
      AddCommGrpCat.{w}
      ((IsAugmentation.abelianStageInverseImage C J K u0 (degree U)).obj G)
      (obj V)).hom ≫
    ((IsAugmentation.abelianStageInverseImage C J K u0 (degree U)).obj G).obj.map
      (homToPair η).2.op

/-- The assembled abelian presheaf on `C_total` whose value at `U` is `a_{deg U}⁻¹ G` at
`obj U`. -/
def IsAugmentation.abelianInverseImagePresheaf
    (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) :
    (totalSite C)ᵒᵖ ⥤ AddCommGrpCat.{w} where
  obj W :=
    ((IsAugmentation.abelianStageInverseImage C J K u0 (degree W.unop)).obj G).obj.obj
      (op (obj W.unop))
  map {W Z} η := IsAugmentation.abelianInverseImagePresheafMap C J K u0 G η.unop
  map_id := sorry
  map_comp := sorry

/-- Inverse image `a⁻¹` of abelian sheaves along the total augmentation morphism. -/
def IsAugmentation.abelianInverseImage :
    Sheaf K.toGrothendieck AddCommGrpCat.{w} ⥤
      Sheaf (topology C J) AddCommGrpCat.{w} where
  obj G := ⟨IsAugmentation.abelianInverseImagePresheaf C J K u0 G, sorry⟩
  map {G H} α := ObjectProperty.homMk
    { app := fun W ↦
        ((IsAugmentation.abelianStageInverseImage C J K u0 (degree W.unop)).map α).hom.app
          (op (obj W.unop))
      naturality := sorry }
  map_id := sorry
  map_comp := sorry

/-- Sections of `a⁻¹ G` over `U` are the sections of `a_{deg U}⁻¹ G` over `obj U`. -/
theorem IsAugmentation.abelianInverseImage_obj_app
    (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) (U : totalSite C) :
    ((IsAugmentation.abelianInverseImage C J K u0).obj G).obj.obj (op U) =
      ((IsAugmentation.abelianStageInverseImage C J K u0 (degree U)).obj G).obj.obj
        (op (obj U)) :=
  sorry

/-- Inverse image of abelian sheaves along the total augmentation is additive. -/
instance IsAugmentation.abelianInverseImage_additive :
    (IsAugmentation.abelianInverseImage C J K u0).Additive :=
  sorry

/-- Inverse image of abelian sheaves along the total augmentation preserves finite limits. -/
instance IsAugmentation.abelianInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (IsAugmentation.abelianInverseImage C J K u0) :=
  sorry

/-- Inverse image of abelian sheaves along the total augmentation preserves finite colimits. -/
instance IsAugmentation.abelianInverseImage_preservesFiniteColimits :
    PreservesFiniteColimits (IsAugmentation.abelianInverseImage C J K u0) :=
  sorry

variable [HasSheafify K.toGrothendieck AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]

/-- Inverse image `a⁻¹` of objects of `D(D)` along the total augmentation morphism. -/
def IsAugmentation.derivedInverseImage :
    DerivedCategory (Sheaf K.toGrothendieck AddCommGrpCat.{w}) ⥤
      DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}) :=
  (IsAugmentation.abelianInverseImage C J K u0).mapDerivedCategory

end CategoryTheory.SimplicialSites
