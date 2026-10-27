/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.AugmentationAbelian

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

/- Stage inverse image `a_n⁻¹` of abelian sheaves, i.e. sheaf pullback along the
common composite `u_n`. -/
#check (CategoryTheory.SimplicialSites.IsAugmentation.abelianStageInverseImage C J K u0 :
    ∀ (n : SimplexCategory),
    Sheaf K.toGrothendieck AddCommGrpCat.{w} ⥤
      Sheaf (J n).toGrothendieck AddCommGrpCat.{w})

/- Inverse-image form of `a_m ∘ f_φ = a_n` on abelian sheaves. -/
#check (CategoryTheory.SimplicialSites.IsAugmentation.abelianStageInverseImage_comp C J K u0 :
    ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    IsAugmentation.abelianStageInverseImage C J K u0 m ⋙
      (C.map φ).toFunctor.sheafPullback AddCommGrpCat.{w}
        (J m).toGrothendieck (J n).toGrothendieck ≅
      IsAugmentation.abelianStageInverseImage C J K u0 n)

/- Pushforward-form transition `a_m⁻¹ G ⟶ (f_φ)_* a_n⁻¹ G` of the abelian inverse-image
system. -/
#check (CategoryTheory.SimplicialSites.IsAugmentation.abelianInverseImageSystemMap C J K u0 :
    ∀ (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) {m n : SimplexCategory} (φ : m ⟶ n),
    (IsAugmentation.abelianStageInverseImage C J K u0 m).obj G ⟶
      ((C.map φ).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{w}
        (J m).toGrothendieck (J n).toGrothendieck).obj
        ((IsAugmentation.abelianStageInverseImage C J K u0 n).obj G))

/- Restriction of the assembled abelian inverse image along a total-category morphism
`(φ, g) : U ⟶ V`. -/
#check (CategoryTheory.SimplicialSites.IsAugmentation.abelianInverseImagePresheafMap C J K u0 :
    ∀ (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) {U V : totalSite C} (η : U ⟶ V),
    ((IsAugmentation.abelianStageInverseImage C J K u0 (degree V)).obj G).obj.obj
      (op (obj V)) ⟶
    ((IsAugmentation.abelianStageInverseImage C J K u0 (degree U)).obj G).obj.obj
      (op (obj U)))

/- The assembled abelian presheaf on `C_total` whose value at `U` is `a_{deg U}⁻¹ G` at
`obj U`. -/
#check (CategoryTheory.SimplicialSites.IsAugmentation.abelianInverseImagePresheaf C J K u0 :
    ∀ (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}),
    (totalSite C)ᵒᵖ ⥤ AddCommGrpCat.{w})

/- Inverse image `a⁻¹` of abelian sheaves along the total augmentation morphism. -/
#check (CategoryTheory.SimplicialSites.IsAugmentation.abelianInverseImage C J K u0 :
    Sheaf K.toGrothendieck AddCommGrpCat.{w} ⥤
      Sheaf (topology C J) AddCommGrpCat.{w})

/- Sections of `a⁻¹ G` over `U` are the sections of `a_{deg U}⁻¹ G` over `obj U`. -/
#check (CategoryTheory.SimplicialSites.IsAugmentation.abelianInverseImage_obj_app C J K u0 :
    ∀ (G : Sheaf K.toGrothendieck AddCommGrpCat.{w}) (U : totalSite C),
    ((IsAugmentation.abelianInverseImage C J K u0).obj G).obj.obj (op U) =
      ((IsAugmentation.abelianStageInverseImage C J K u0 (degree U)).obj G).obj.obj
        (op (obj U)))

/- Inverse image of abelian sheaves along the total augmentation is additive. -/
#check (CategoryTheory.SimplicialSites.IsAugmentation.abelianInverseImage_additive C J K u0 :
    (IsAugmentation.abelianInverseImage C J K u0).Additive)

/- Inverse image of abelian sheaves along the total augmentation preserves finite limits. -/
#check (CategoryTheory.SimplicialSites.IsAugmentation.abelianInverseImage_preservesFiniteLimits C J K u0 :
    PreservesFiniteLimits (IsAugmentation.abelianInverseImage C J K u0))

/- Inverse image of abelian sheaves along the total augmentation preserves finite colimits. -/
#check (CategoryTheory.SimplicialSites.IsAugmentation.abelianInverseImage_preservesFiniteColimits C J K u0 :
    PreservesFiniteColimits (IsAugmentation.abelianInverseImage C J K u0))

variable [HasSheafify K.toGrothendieck AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]

/- Inverse image `a⁻¹` of objects of `D(D)` along the total augmentation morphism. -/
#check (CategoryTheory.SimplicialSites.IsAugmentation.derivedInverseImage C J K u0 :
    DerivedCategory (Sheaf K.toGrothendieck AddCommGrpCat.{w}) ⥤
      DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))

end CategoryTheory.SimplicialSites
