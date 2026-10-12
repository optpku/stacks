/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap85.Lemma_85_4_2_MorphismDiagram
public import stacks_project.Chap85.Lemma_85_5_2_Total
public import stacks_project.Chap85.Remark_85_5_4_MorphismDiagram

/-!
# Total inverse-image square of a compatible morphism of simplicial sites

In Situation 85.3.3 case A, compatibility of `h₋₁` with a morphism of simplicial
sites and a pair of augmentations lifts from the degree-zero square to a
canonical isomorphism `(a')⁻¹ ⋙ h_total⁻¹ ≅ h₋₁⁻¹ ⋙ a⁻¹` of inverse images of
the total morphisms of topoi.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MorphismOfTopoiIn Simplicial

noncomputable section

namespace CategoryTheory.SimplicialSites

section

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
variable [HasEqualizers (Sheaf K.toGrothendieck (Type w))]
variable [h_morphism : IsMorphismDiagram C J]
variable [h_aug : IsAugmentation C J K u0]
include h_morphism h_aug

/-- The presenting functor `u_0` of the degree-zero stage is isomorphic to `u0`, by the
identity law `SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙`. -/
def IsAugmentation.stageFunctor_zeroIso :
    IsAugmentation.stageFunctor C u0 ⦋0⦌ ≅ u0 :=
  Functor.isoWhiskerLeft u0
      (Cat.Hom.toNatIso (eqToIso (congrArg C.map SimplexCategory.const_eq_id)) ≪≫
        Cat.Hom.toNatIso (eqToIso (C.map_id ⦋0⦌)) ≪≫
        eqToIso Cat.Hom.id_toFunctor) ≪≫
    Functor.rightUnitor u0

/-- Inverse images of `a_0` presented by `stageFunctor ⦋0⦌` and by `u0` are canonically
isomorphic. -/
def IsAugmentation.stageTopos_zero :
    (IsAugmentation.stageTopos C J K u0 ⦋0⦌)⁻¹ ≅
      (IsAugmentation.toposMap C J K u0)⁻¹ :=
  -- Local instance justification (search instability): IsContinuous of this presenting stageFunctor is a parent of IsAugmentation.stageFunctor_isExactMorphism, whose extra C/J/u0 parameters cannot be synthesized from the functor alone.
  letI : (IsAugmentation.stageFunctor C u0 ⦋0⦌).IsContinuous
      K.toGrothendieck (J ⦋0⦌).toGrothendieck :=
    (IsAugmentation.stageFunctor_isExactMorphism C J K u0 ⦋0⦌).toIsContinuous
  Adjunction.leftAdjointUniq
    (((IsAugmentation.stageFunctor C u0 ⦋0⦌).sheafAdjunctionContinuous (Type w)
        K.toGrothendieck (J ⦋0⦌).toGrothendieck).ofNatIsoRight
      (Functor.sheafPushforwardContinuousIso
        (IsAugmentation.stageFunctor_zeroIso C u0) (Type w)
        K.toGrothendieck (J ⦋0⦌).toGrothendieck))
    (u0.sheafAdjunctionContinuous (Type w) K.toGrothendieck (J ⦋0⦌).toGrothendieck)

variable [∀ n, (ofStage C n).IsContinuous (J n).toGrothendieck (topology C J)]

/-- Restriction to degree `n` agrees with continuous sheaf pushforward along `ofStage`,
by the identity on sections. -/
def restrictToDegree_iso_stageRestrict (n : SimplexCategory) :
    restrictToDegree C J n ≅ stageRestrict C J (Type w) n :=
  NatIso.ofComponents
    (fun F ↦
      { hom := ObjectProperty.homMk { app := fun _ ↦ 𝟙 _, naturality := sorry }
        inv := ObjectProperty.homMk { app := fun _ ↦ 𝟙 _, naturality := sorry }
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

end

section

variable {C C' : SimplexCategory ⥤ Cat.{v, u}}
variable (J : ∀ n, Precoverage (C.obj n)) (J' : ∀ n, Precoverage (C'.obj n))
variable {D : Type u} [Category.{v} D] (K : Precoverage D)
variable {D' : Type u} [Category.{v} D'] (K' : Precoverage D')
variable (u0 : D ⥤ C.obj ⦋0⦌) (u0' : D' ⥤ C'.obj ⦋0⦌)
variable (α : C' ⟶ C) (v : D' ⥤ D)
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J' n).toGrothendieck (Type w)]
variable [HasWeakSheafify K.toGrothendieck (Type w)]
variable [HasWeakSheafify K'.toGrothendieck (Type w)]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [HasWeakSheafify (topology C' J') (Type w)]
variable [HasSheafify (topology C J) (Type w)]
variable [HasSheafify (topology C' J') (Type w)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasSheafify (J' n).toGrothendieck (Type w)]
variable [HasEqualizers (Sheaf K.toGrothendieck (Type w))]
variable [HasEqualizers (Sheaf K'.toGrothendieck (Type w))]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C'.obj m)ᵒᵖ ⥤ Type w),
    ((C'.map φ).toFunctor).op.HasLeftKanExtension P]
variable [∀ P : Dᵒᵖ ⥤ Type w, u0.op.HasLeftKanExtension P]
variable [∀ P : D'ᵒᵖ ⥤ Type w, u0'.op.HasLeftKanExtension P]
variable [∀ (n : SimplexCategory) (P : Dᵒᵖ ⥤ Type w),
    (IsAugmentation.stageFunctor C u0 n).op.HasLeftKanExtension P]
variable [∀ (n : SimplexCategory) (P : D'ᵒᵖ ⥤ Type w),
    (IsAugmentation.stageFunctor C' u0' n).op.HasLeftKanExtension P]
variable [∀ n (P : (C'.obj n)ᵒᵖ ⥤ Type w), ((α.app n).toFunctor).op.HasLeftKanExtension P]
variable [∀ P : D'ᵒᵖ ⥤ Type w, v.op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (C'.obj n)ᵒᵖ ⥤ Type w, (ofStage C' n).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (C'.obj n)ᵒᵖ ⥤ Type w, (ofStage C' n).op.HasPointwiseRightKanExtension P]
variable [∀ P : (totalSite C')ᵒᵖ ⥤ Type w, ((IsMorphism.totalFunctor α).op).HasLeftKanExtension P]
variable [instC : IsMorphismDiagram C J] [instC' : IsMorphismDiagram C' J']
variable [hα : IsMorphism J J' α]
variable [h_aug : IsAugmentation C J K u0] [h_aug' : IsAugmentation C' J' K' u0']
variable [h : IsCompatible J J' K K' u0 u0' α v]
include instC instC' hα h_aug h_aug' h

/-- Inverse-image form of `a'_n ∘ h_n = h₋₁ ∘ a_n`, obtained by transporting the degree-zero
compatibility square along `φ = SimplexCategory.const ⦋0⦌ n 0`. -/
def IsCompatible.stageInverseImage_comp (n : SimplexCategory) :
    (IsAugmentation.stageTopos C' J' K' u0' n)⁻¹ ⋙ (IsMorphism.topos J J' α n)⁻¹ ≅
      (IsCompatible.topos J J' K K' u0 u0' α v)⁻¹ ⋙
        (IsAugmentation.stageTopos C J K u0 n)⁻¹ :=
  let φ : ⦋0⦌ ⟶ n := SimplexCategory.const ⦋0⦌ n 0
  Functor.isoWhiskerRight
      (IsAugmentation.stageTopos_comp C' J' K' u0' φ).symm
      (IsMorphism.topos J J' α n).inverseImage ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (IsAugmentation.stageTopos C' J' K' u0' ⦋0⦌).inverseImage
      (IsMorphism.inverseImage_naturality J J' α φ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (IsAugmentation.stageTopos_zero C' J' K' u0')
        (IsMorphism.topos J J' α ⦋0⦌).inverseImage)
      (toposMap C J φ).inverseImage ≪≫
    Functor.isoWhiskerRight (IsCompatible.inverseImage_comp J J' K K' u0 u0' α v)
      (toposMap C J φ).inverseImage ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (IsCompatible.topos J J' K K' u0 u0' α v).inverseImage
      (Functor.isoWhiskerRight (IsAugmentation.stageTopos_zero C J K u0).symm
        (toposMap C J φ).inverseImage) ≪≫
    Functor.isoWhiskerLeft (IsCompatible.topos J J' K K' u0 u0' α v).inverseImage
      (IsAugmentation.stageTopos_comp C J K u0 φ)

variable [∀ n, (ofStage C n).IsCocontinuous (J n).toGrothendieck (topology C J)]
variable [∀ n, (ofStage C' n).IsCocontinuous (J' n).toGrothendieck (topology C' J')]
variable [∀ n, (ofStage C n).IsContinuous (J n).toGrothendieck (topology C J)]
variable [∀ n, (ofStage C' n).IsContinuous (J' n).toGrothendieck (topology C' J')]

/-- Restriction of the total inverse-image square along `g_n⁻¹`, identified with the
degree-`n` square by `IsMorphism.inverseImage_comp` and
`IsAugmentation.totalTopos_comp_ofStage`. -/
def IsCompatible.totalInverseImage_comp_ofStage (n : SimplexCategory) :
    ((IsAugmentation.totalTopos C' J' K' u0')⁻¹ ⋙ (IsMorphism.total J J' α)⁻¹) ⋙
        (ofStageMorphism C J n)⁻¹ ≅
      ((IsCompatible.topos J J' K K' u0 u0' α v)⁻¹ ⋙
          (IsAugmentation.totalTopos C J K u0)⁻¹) ⋙
        (ofStageMorphism C J n)⁻¹ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (IsAugmentation.totalTopos C' J' K' u0').inverseImage
      (IsMorphism.inverseImage_comp J J' α n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (IsAugmentation.totalTopos_comp_ofStage C' J' K' u0' n)
      (IsMorphism.topos J J' α n).inverseImage ≪≫
    IsCompatible.stageInverseImage_comp J J' K K' u0 u0' α v n ≪≫
    Functor.isoWhiskerLeft (IsCompatible.topos J J' K K' u0 u0' α v).inverseImage
      (IsAugmentation.totalTopos_comp_ofStage C J K u0 n).symm ≪≫
    (Functor.associator _ _ _).symm

/-- Degree-`n` restriction of the two total inverse-image composites. -/
def IsCompatible.totalInverseImage_comp_restrict (n : SimplexCategory)
    (G : Sheaf K'.toGrothendieck (Type w)) :
    (restrictToDegree C J n).obj
        (((IsAugmentation.totalTopos C' J' K' u0')⁻¹ ⋙
            (IsMorphism.total J J' α)⁻¹).obj G) ≅
      (restrictToDegree C J n).obj
        (((IsCompatible.topos J J' K K' u0 u0' α v)⁻¹ ⋙
            (IsAugmentation.totalTopos C J K u0)⁻¹).obj G) :=
  (restrictToDegree_iso_stageRestrict C J n).app _ ≪≫
    (ofStageMorphism_inverseImage_iso_stageRestrict C J n).symm.app _ ≪≫
    (IsCompatible.totalInverseImage_comp_ofStage J J' K K' u0 u0' α v n).app G ≪≫
    (ofStageMorphism_inverseImage_iso_stageRestrict C J n).app _ ≪≫
    (restrictToDegree_iso_stageRestrict C J n).symm.app _

/-- Sheaf-system comparison whose degree-`n` component is
`IsCompatible.totalInverseImage_comp_restrict`. -/
def IsCompatible.totalInverseImage_comp_system (G : Sheaf K'.toGrothendieck (Type w)) :
    (toSheafSystem C J).obj
        (((IsAugmentation.totalTopos C' J' K' u0')⁻¹ ⋙
            (IsMorphism.total J J' α)⁻¹).obj G) ≅
      (toSheafSystem C J).obj
        (((IsCompatible.topos J J' K K' u0 u0' α v)⁻¹ ⋙
            (IsAugmentation.totalTopos C J K u0)⁻¹).obj G) where
  hom :=
    SheafSystem.homMk
      (fun n ↦
        (IsCompatible.totalInverseImage_comp_restrict J J' K K' u0 u0' α v n G).hom)
      sorry
  inv :=
    SheafSystem.homMk
      (fun n ↦
        (IsCompatible.totalInverseImage_comp_restrict J J' K K' u0 u0' α v n G).inv)
      sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Inverse-image form of `a' ∘ h_total = h₋₁ ∘ a` as morphisms of topoi
`Sh(C_total) ⟶ Sh(D')`. -/
def IsCompatible.totalInverseImage_comp :
    (IsAugmentation.totalTopos C' J' K' u0')⁻¹ ⋙ (IsMorphism.total J J' α)⁻¹ ≅
      (IsCompatible.topos J J' K K' u0 u0' α v)⁻¹ ⋙
        (IsAugmentation.totalTopos C J K u0)⁻¹ :=
  NatIso.ofComponents
    (fun G ↦
      (unitIso C J).app _ ≪≫
        (ofSheafSystem C J).mapIso
          (IsCompatible.totalInverseImage_comp_system J J' K K' u0 u0' α v G) ≪≫
        ((unitIso C J).app _).symm)
    sorry

end

end CategoryTheory.SimplicialSites


