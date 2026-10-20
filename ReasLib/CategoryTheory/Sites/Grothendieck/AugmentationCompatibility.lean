module

public import ReasLib.CategoryTheory.Sites.Grothendieck.AugmentationTopos
public import ReasLib.CategoryTheory.Sites.Grothendieck.SimplicialTotalMorphism
public import ReasLib.CategoryTheory.Sites.Grothendieck.SimplicialCompatibility

/-!
# Compatibility of total simplicial augmentations

Degree-zero compatibility of augmented simplicial sites induces a canonical
comparison of the total inverse-image functors.
-/

set_option backward.privateInPublic true

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MorphismOfTopoiIn Simplicial

noncomputable section

namespace CategoryTheory.Grothendieck

section

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
include h_fiberwise h_aug

variable [∀ P : (F.obj (op ⦋0⦌))ᵒᵖ ⥤ Type w, u0.op.HasPointwiseRightKanExtension P]

/-- The presenting functor `u_0` of the degree-zero stage is isomorphic to `u0`, by the
identity law `SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙`. -/
private def IsAugmentation.stageFunctor_zeroIso :
    IsAugmentation.stageFunctor F u0 ⦋0⦌ ≅ u0 :=
  Functor.isoWhiskerRight
      (Cat.Hom.toNatIso
          (eqToIso (congrArg (fun φ : ⦋0⦌ ⟶ ⦋0⦌ ↦ F.map φ.op)
            SimplexCategory.const_eq_id)) ≪≫
        Cat.Hom.toNatIso (eqToIso (F.map_id (op ⦋0⦌))) ≪≫
        eqToIso Cat.Hom.id_toFunctor)
      u0 ≪≫
    Functor.leftUnitor u0

/-- Inverse images of `a_0` presented by `stageFunctor ⦋0⦌` and by `u0` are canonically
isomorphic. -/
private def IsAugmentation.stageTopos_zero :
    (IsAugmentation.stageTopos F J K u0 ⦋0⦌)⁻¹ ≅
      u0.sheafPullbackCocontinuous (Type w) (J (op ⦋0⦌)).toGrothendieck K.toGrothendieck :=
  let hu0 : u0.IsCocontinuous (J (op ⦋0⦌)).toGrothendieck K.toGrothendieck :=
    @Functor.Precoverage.IsCocontinuous.toCocontinuousOfCoverBasis
      _ _ _ _ _ _ u0 h_aug.isCocontinuous
      (fun hS ↦ Precoverage.HasFactoringPullbacks.exists_generate_le (J := K) hS)
  let hs := IsAugmentation.stageFunctor_isCocontinuous F J K u0 ⦋0⦌
  Adjunction.leftAdjointUniq
    ((@Functor.sheafPullbackCocontinuousAdjunction _ _ _ _
        (IsAugmentation.stageFunctor F u0 ⦋0⦌)
        (J (op ⦋0⦌)).toGrothendieck K.toGrothendieck hs _ _).ofNatIsoRight
      (@Functor.sheafPushforwardCocontinuousIso _ _ _ _
        (J (op ⦋0⦌)).toGrothendieck K.toGrothendieck
        (IsAugmentation.stageFunctor F u0 ⦋0⦌) hs (Type w) _ _ u0
        (IsAugmentation.stageFunctor_zeroIso F u0) hu0 _))
    (@Functor.sheafPullbackCocontinuousAdjunction _ _ _ _ u0
      (J (op ⦋0⦌)).toGrothendieck K.toGrothendieck hu0 _ _)

variable [∀ n, (ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)]

omit h_aug in
/-- The identity maps between the two restriction presentations commute with stage morphisms. -/
private theorem restrictToDegree_iso_fiberRestrict_naturality (n : SimplexCategory)
    (G : Sheaf (topology F J) (Type w))
    {V W : (F.obj (op n))ᵒᵖ} (η : V ⟶ W) :
    (((restrictToDegree F J n).obj G).obj.map η ≫ 𝟙 _ =
      𝟙 _ ≫ ((fiberRestrict F J (Type w) n).obj G).obj.map η) ∧
    (((fiberRestrict F J (Type w) n).obj G).obj.map η ≫ 𝟙 _ =
      𝟙 _ ≫ ((restrictToDegree F J n).obj G).obj.map η) := by
  sorry

/-- Restriction to degree `n` agrees with continuous sheaf pushforward along `ι`,
by the identity on sections. -/
private def restrictToDegree_iso_fiberRestrict (n : SimplexCategory) :
    restrictToDegree F J n ≅ fiberRestrict F J (Type w) n :=
  NatIso.ofComponents
    (fun G ↦
      { hom := ObjectProperty.homMk
          { app := fun _ ↦ 𝟙 _
            naturality := by
              intro V W η
              exact (restrictToDegree_iso_fiberRestrict_naturality F J n G η).1 }
        inv := ObjectProperty.homMk
          { app := fun _ ↦ 𝟙 _
            naturality := by
              intro V W η
              exact (restrictToDegree_iso_fiberRestrict_naturality F J n G η).2 }
        hom_inv_id := by ext V x; rfl
        inv_hom_id := by ext V x; rfl })
    (by intro G H f; ext V x; rfl)

end

section

variable {F F' : SimplicialObject Cat.{v, u}}
variable (J : ∀ n, Precoverage (F.obj n)) (J' : ∀ n, Precoverage (F'.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable {D' : Type u} [Category.{v} D'] (K' : Precoverage D')
variable (u0 : F.obj (op ⦋0⦌) ⥤ D) (u0' : F'.obj (op ⦋0⦌) ⥤ D')
variable (α : F ⟶ F') (v : D ⥤ D')
variable [instF : IsFiberwiseSite F J] [instF' : IsFiberwiseSite F' J']
variable [hα : IsFiberwiseMorphism J J' α]
variable [h_aug : IsAugmentation F J K u0] [h_aug' : IsAugmentation F' J' K' u0']
variable [h : IsCompatible J J' K K' u0 u0' α v]
include instF instF' hα h_aug h_aug' h
variable [K.IsSite] [K'.IsSite]
variable [∀ n, (J n).IsSite] [∀ n, (J' n).IsSite]
variable [(J (op ⦋0⦌)).IsSite] [(J' (op ⦋0⦌)).IsSite]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasSheafify (J' n).toGrothendieck (Type w)]
variable [HasSheafify K.toGrothendieck (Type w)]
variable [HasSheafify K'.toGrothendieck (Type w)]
variable [HasWeakSheafify K.toGrothendieck (Type w)]
variable [HasWeakSheafify K'.toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [HasSheafify (topology F' J') (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [HasWeakSheafify (topology F' J') (Type w)]
variable [HasEqualizers (Sheaf K.toGrothendieck (Type w))]
variable [HasEqualizers (Sheaf K'.toGrothendieck (Type w))]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J' n).toGrothendieck (Type w)]
variable [∀ (n : SimplexCategory) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    (IsAugmentation.stageFunctor F u0 n).op.HasPointwiseRightKanExtension P]
variable [∀ (n : SimplexCategory) (P : (F'.obj (op n))ᵒᵖ ⥤ Type w),
    (IsAugmentation.stageFunctor F' u0' n).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F'.obj (op n))ᵒᵖ ⥤ Type w),
    ((F'.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (F'.obj (op n))ᵒᵖ ⥤ Type w, (ι F' (op n)).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F'.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F' (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n (P : (F.obj n)ᵒᵖ ⥤ Type w),
    ((α.app n).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
    (Grothendieck.map α).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    ((α.app (op n)).toFunctor ⋙ ι F' (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n) ⋙ Grothendieck.map α).op.HasPointwiseRightKanExtension P]
variable [∀ P : (F.obj (op ⦋0⦌))ᵒᵖ ⥤ Type w, u0.op.HasPointwiseRightKanExtension P]
variable [∀ P : (F'.obj (op ⦋0⦌))ᵒᵖ ⥤ Type w, u0'.op.HasPointwiseRightKanExtension P]
variable [∀ P : Dᵒᵖ ⥤ Type w, v.op.HasPointwiseRightKanExtension P]
variable [∀ P : (F.obj (op ⦋0⦌))ᵒᵖ ⥤ Type w, (u0 ⋙ v).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor ⋙ (α.app (op m)).toFunctor).op.HasPointwiseRightKanExtension P]

/-- Inverse-image form of `a'_n ∘ h_n = h₋₁ ∘ a_n`, obtained by transporting the degree-zero
compatibility square along `φ = SimplexCategory.const ⦋0⦌ n 0`. -/
def IsCompatible.stageInverseImage_comp (n : SimplexCategory) :
    (IsAugmentation.stageTopos F' J' K' u0' n)⁻¹ ⋙
        (IsFiberwiseMorphism.topos J J' α n)⁻¹ ≅
      (IsCompatible.topos J J' K K' u0 u0' α v)⁻¹ ⋙
        (IsAugmentation.stageTopos F J K u0 n)⁻¹ :=
  let φ : ⦋0⦌ ⟶ n := SimplexCategory.const ⦋0⦌ n 0
  Functor.isoWhiskerRight
      (IsAugmentation.stageTopos_comp F' J' K' u0' φ).symm
      (IsFiberwiseMorphism.topos J J' α n).inverseImage ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (IsAugmentation.stageTopos F' J' K' u0' ⦋0⦌).inverseImage
      (IsFiberwiseMorphism.inverseImage_naturality J J' α φ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (IsAugmentation.stageTopos_zero F' J' K' u0')
        (IsFiberwiseMorphism.topos J J' α ⦋0⦌).inverseImage)
      (toposMap F J φ).inverseImage ≪≫
    Functor.isoWhiskerRight (IsCompatible.inverseImage_comp J J' K K' u0 u0' α v)
      (toposMap F J φ).inverseImage ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (IsCompatible.topos J J' K K' u0 u0' α v).inverseImage
      (Functor.isoWhiskerRight (IsAugmentation.stageTopos_zero F J K u0).symm
        (toposMap F J φ).inverseImage) ≪≫
    Functor.isoWhiskerLeft (IsCompatible.topos J J' K K' u0 u0' α v).inverseImage
      (IsAugmentation.stageTopos_comp F J K u0 φ)

variable [∀ n, (ι F (op n)).IsCocontinuous (J (op n)).toGrothendieck (topology F J)]
variable [∀ n, (ι F' (op n)).IsCocontinuous (J' (op n)).toGrothendieck (topology F' J')]
variable [∀ n, (ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)]
variable [∀ n, (ι F' (op n)).IsContinuous (J' (op n)).toGrothendieck (topology F' J')]

/-- Restriction of the total inverse-image square along `g_n⁻¹`, identified with the
degree-`n` square by `IsFiberwiseMorphism.inverseImage_comp` and
`IsAugmentation.totalTopos_comp_fiberMorphism`. -/
def IsCompatible.totalInverseImage_comp_fiberMorphism (n : SimplexCategory) :
    ((IsAugmentation.totalTopos F' J' K' u0')⁻¹ ⋙
        (IsFiberwiseMorphism.total J J' α)⁻¹) ⋙ (fiberMorphism F J n)⁻¹ ≅
      ((IsCompatible.topos J J' K K' u0 u0' α v)⁻¹ ⋙
          (IsAugmentation.totalTopos F J K u0)⁻¹) ⋙ (fiberMorphism F J n)⁻¹ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (IsAugmentation.totalTopos F' J' K' u0').inverseImage
      (IsFiberwiseMorphism.inverseImage_comp J J' α n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (IsAugmentation.totalTopos_comp_fiberMorphism F' J' K' u0' n)
      (IsFiberwiseMorphism.topos J J' α n).inverseImage ≪≫
    IsCompatible.stageInverseImage_comp J J' K K' u0 u0' α v n ≪≫
    Functor.isoWhiskerLeft (IsCompatible.topos J J' K K' u0 u0' α v).inverseImage
      (IsAugmentation.totalTopos_comp_fiberMorphism F J K u0 n).symm ≪≫
    (Functor.associator _ _ _).symm

/-- Degree-`n` restriction of the two total inverse-image composites. -/
private def IsCompatible.totalInverseImage_comp_restrict (n : SimplexCategory)
    (G : Sheaf K'.toGrothendieck (Type w)) :
    (restrictToDegree F J n).obj
        (((IsAugmentation.totalTopos F' J' K' u0')⁻¹ ⋙
            (IsFiberwiseMorphism.total J J' α)⁻¹).obj G) ≅
      (restrictToDegree F J n).obj
        (((IsCompatible.topos J J' K K' u0 u0' α v)⁻¹ ⋙
            (IsAugmentation.totalTopos F J K u0)⁻¹).obj G) :=
  (restrictToDegree_iso_fiberRestrict F J n).app _ ≪≫
    (fiberMorphism_inverseImage_iso_fiberRestrict F J n).symm.app _ ≪≫
    (IsCompatible.totalInverseImage_comp_fiberMorphism J J' K K' u0 u0' α v n).app G ≪≫
    (fiberMorphism_inverseImage_iso_fiberRestrict F J n).app _ ≪≫
    (restrictToDegree_iso_fiberRestrict F J n).symm.app _

/-- The degreewise comparisons and their inverses respect the sheaf-system transitions. -/
private theorem IsCompatible.totalInverseImage_comp_system_naturality
    (G : Sheaf K'.toGrothendieck (Type w)) :
    let S := (toSheafSystem F J).obj (((IsAugmentation.totalTopos F' J' K' u0')⁻¹ ⋙ (IsFiberwiseMorphism.total J J' α)⁻¹).obj G)
    let T := (toSheafSystem F J).obj (((IsCompatible.topos J J' K K' u0 u0' α v)⁻¹ ⋙ (IsAugmentation.totalTopos F J K u0)⁻¹).obj G)
    (∀ {m n : SimplexCategory} (φ : m ⟶ n),
      S.map φ ≫ (toposMap F J φ).pushforward.map ((IsCompatible.totalInverseImage_comp_restrict J J' K K' u0 u0' α v n G).hom) =
        (IsCompatible.totalInverseImage_comp_restrict J J' K K' u0 u0' α v m G).hom ≫ T.map φ) ∧
    (∀ {m n : SimplexCategory} (φ : m ⟶ n),
      T.map φ ≫ (toposMap F J φ).pushforward.map ((IsCompatible.totalInverseImage_comp_restrict J J' K K' u0 u0' α v n G).inv) =
        (IsCompatible.totalInverseImage_comp_restrict J J' K K' u0 u0' α v m G).inv ≫ S.map φ) := by
  sorry

/-- Sheaf-system comparison whose degree-`n` component is
`IsCompatible.totalInverseImage_comp_restrict`. -/
private def IsCompatible.totalInverseImage_comp_system (G : Sheaf K'.toGrothendieck (Type w)) :
    (toSheafSystem F J).obj
        (((IsAugmentation.totalTopos F' J' K' u0')⁻¹ ⋙
            (IsFiberwiseMorphism.total J J' α)⁻¹).obj G) ≅
      (toSheafSystem F J).obj
        (((IsCompatible.topos J J' K K' u0 u0' α v)⁻¹ ⋙
            (IsAugmentation.totalTopos F J K u0)⁻¹).obj G) where
  hom :=
    SimplicialSites.SheafSystem.homMk
      (fun n ↦
        (IsCompatible.totalInverseImage_comp_restrict J J' K K' u0 u0' α v n G).hom)
      (IsCompatible.totalInverseImage_comp_system_naturality J J' K K' u0 u0' α v G).1
  inv :=
    SimplicialSites.SheafSystem.homMk
      (fun n ↦
        (IsCompatible.totalInverseImage_comp_restrict J J' K K' u0 u0' α v n G).inv)
      (IsCompatible.totalInverseImage_comp_system_naturality J J' K K' u0 u0' α v G).2
  hom_inv_id := by
    apply SimplicialSites.SheafSystem.Hom.ext
    intro n
    exact (IsCompatible.totalInverseImage_comp_restrict J J' K K' u0 u0' α v n G).hom_inv_id
  inv_hom_id := by
    apply SimplicialSites.SheafSystem.Hom.ext
    intro n
    exact (IsCompatible.totalInverseImage_comp_restrict J J' K K' u0 u0' α v n G).inv_hom_id

/-- The assembled total comparison commutes with morphisms of input sheaves. -/
private theorem IsCompatible.totalInverseImage_comp_naturality
    {G H : Sheaf K'.toGrothendieck (Type w)} (f : G ⟶ H) :
    ((IsAugmentation.totalTopos F' J' K' u0')⁻¹ ⋙ (IsFiberwiseMorphism.total J J' α)⁻¹).map f ≫
      ((unitIso F J).app _ ≪≫
        (ofSheafSystem F J).mapIso
          (IsCompatible.totalInverseImage_comp_system J J' K K' u0 u0' α v H) ≪≫
        ((unitIso F J).app _).symm).hom =
      ((unitIso F J).app _ ≪≫
        (ofSheafSystem F J).mapIso
          (IsCompatible.totalInverseImage_comp_system J J' K K' u0 u0' α v G) ≪≫
        ((unitIso F J).app _).symm).hom ≫ ((IsCompatible.topos J J' K K' u0 u0' α v)⁻¹ ⋙ (IsAugmentation.totalTopos F J K u0)⁻¹).map f := by
  sorry

/-- Inverse-image form of `a' ∘ h_total = h₋₁ ∘ a` as morphisms of topoi
`Sh(C_total) ⟶ Sh(D')`. -/
def IsCompatible.totalInverseImage_comp :
    (IsAugmentation.totalTopos F' J' K' u0')⁻¹ ⋙
        (IsFiberwiseMorphism.total J J' α)⁻¹ ≅
      (IsCompatible.topos J J' K K' u0 u0' α v)⁻¹ ⋙
        (IsAugmentation.totalTopos F J K u0)⁻¹ :=
  NatIso.ofComponents
    (fun G ↦
      (unitIso F J).app _ ≪≫
        (ofSheafSystem F J).mapIso
          (IsCompatible.totalInverseImage_comp_system J J' K K' u0 u0' α v G) ≪≫
        ((unitIso F J).app _).symm)
    (fun f ↦ IsCompatible.totalInverseImage_comp_naturality J J' K K' u0 u0' α v f)

end

end CategoryTheory.Grothendieck
