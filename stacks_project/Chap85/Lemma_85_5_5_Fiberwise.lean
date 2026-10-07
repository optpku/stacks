module

public import stacks_project.Chap85.Lemma_85_4_2_Fiberwise
public import stacks_project.Chap85.Lemma_85_5_2_Fiberwise
public import stacks_project.Chap85.Remark_85_5_4_Fiberwise

/-!
# Total inverse-image square of a compatible fiberwise morphism

In Situation 85.3.3 case B, compatibility of `h₋₁` with a fiberwise morphism of
simplicial sites and a pair of augmentations lifts from the degree-zero square
to a canonical isomorphism `(a')⁻¹ ⋙ h_total⁻¹ ≅ h₋₁⁻¹ ⋙ a⁻¹` of inverse
images of the total morphisms of topoi.
-/

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
def IsAugmentation.stageFunctor_zeroIso :
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
def IsAugmentation.stageTopos_zero :
    (IsAugmentation.stageTopos F J K u0 ⦋0⦌)⁻¹ ≅
      (IsAugmentation.toposMap F J K u0)⁻¹ :=
  Adjunction.leftAdjointUniq
    (((IsAugmentation.stageFunctor F u0 ⦋0⦌).sheafPullbackCocontinuousAdjunction
        (J (op ⦋0⦌)).toGrothendieck K.toGrothendieck).ofNatIsoRight
      (Functor.sheafPushforwardCocontinuousIso
        (J (op ⦋0⦌)).toGrothendieck K.toGrothendieck
        (IsAugmentation.stageFunctor F u0 ⦋0⦌)
        (IsAugmentation.stageFunctor_zeroIso F u0)))
    (u0.sheafPullbackCocontinuousAdjunction
      (J (op ⦋0⦌)).toGrothendieck K.toGrothendieck)

variable [∀ n, (ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)]

/-- Restriction to degree `n` agrees with continuous sheaf pushforward along `ι`,
by the identity on sections. -/
def restrictToDegree_iso_fiberRestrict (n : SimplexCategory) :
    restrictToDegree F J n ≅ fiberRestrict F J (Type w) n :=
  NatIso.ofComponents
    (fun G ↦
      { hom := ObjectProperty.homMk { app := fun _ ↦ 𝟙 _, naturality := sorry }
        inv := ObjectProperty.homMk { app := fun _ ↦ 𝟙 _, naturality := sorry }
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

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
    (IsFiberwiseMorphism.totalFunctor α).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    ((α.app (op n)).toFunctor ⋙ ι F' (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n) ⋙ IsFiberwiseMorphism.totalFunctor α).op.HasPointwiseRightKanExtension P]
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
def IsCompatible.totalInverseImage_comp_restrict (n : SimplexCategory)
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

/-- Sheaf-system comparison whose degree-`n` component is
`IsCompatible.totalInverseImage_comp_restrict`. -/
def IsCompatible.totalInverseImage_comp_system (G : Sheaf K'.toGrothendieck (Type w)) :
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
      sorry
  inv :=
    SimplicialSites.SheafSystem.homMk
      (fun n ↦
        (IsCompatible.totalInverseImage_comp_restrict J J' K K' u0 u0' α v n G).inv)
      sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

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
    sorry

end

end CategoryTheory.Grothendieck
