/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import stacks_project.Chap85.Lemma_85_3_5
public import stacks_project.Chap85.Remark_85_5_1_Morphism

/-!
# Total topos morphism of a fiberwise morphism of simplicial sites (case B)

A morphism of simplicial sites `α : F ⟶ F'` in the fiberwise presentation induces a
cocontinuous functor of total sites `Grothendieck.map α`, and hence a morphism of topoi
`h_total : Sh(C_total) ⟶ Sh(C'_total)`.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MorphismOfTopoiIn

noncomputable section

namespace CategoryTheory.Grothendieck

variable {F F' : SimplicialObject Cat.{v, u}}
variable (J : ∀ n, Precoverage (F.obj n)) (J' : ∀ n, Precoverage (F'.obj n))
variable [instF : IsFiberwiseSite F J] [instF' : IsFiberwiseSite F' J']
variable (α : F ⟶ F')
variable [hα : IsFiberwiseMorphism J J' α]
include instF instF' hα

namespace IsFiberwiseMorphism

/-- The functor `v_total : C_total ⥤ C'_total` obtained by applying the component functors
of `α` in each degree. -/
def totalFunctor : Grothendieck F ⥤ Grothendieck F' :=
  Grothendieck.map α

/-- `totalFunctor` sends a Grothendieck object `⟨b, x⟩` to `⟨b, (α.app b).toFunctor.obj x⟩`. -/
theorem totalFunctor_obj (X : Grothendieck F) :
    (totalFunctor α).obj X = ⟨X.base, (α.app X.base).toFunctor.obj X.fiber⟩ :=
  sorry

/-- The fiber inclusion of `F` followed by `v_total` is the component functor followed by
the fiber inclusion of `F'`. -/
def totalFunctor_comp_ι (n : SimplexCategory) :
    ι F (op n) ⋙ totalFunctor α ≅ (α.app (op n)).toFunctor ⋙ ι F' (op n) :=
  Grothendieck.ιCompMap α (op n)

/-- `totalFunctor_comp_ι` is the identity on objects. -/
theorem totalFunctor_comp_ι_hom_app (n : SimplexCategory) (U : F.obj (op n)) :
    (totalFunctor_comp_ι α n).hom.app U = 𝟙 _ :=
  sorry

variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasSheafify (J' n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [HasSheafify (topology F' J') (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [HasWeakSheafify (topology F' J') (Type w)]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (F'.obj (op n))ᵒᵖ ⥤ Type w, (ι F' (op n)).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F'.obj (op n))ᵒᵖ ⥤ Type w, (ι F' (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n (P : (F.obj n)ᵒᵖ ⥤ Type w),
    ((α.app n).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w, (totalFunctor α).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    ((α.app (op n)).toFunctor ⋙ ι F' (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n) ⋙ totalFunctor α).op.HasPointwiseRightKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J' n).toGrothendieck (Type w)]

/-- `v_total` is cocontinuous for the identity-degree total topologies of Lemma 85.3.2. -/
instance instTotalFunctorIsCocontinuous :
    (totalFunctor α).IsCocontinuous (topology F J) (topology F' J') :=
  sorry

/-- The composite `ι F (op n) ⋙ v_total` is cocontinuous. -/
instance instTotalFunctorCompιIsCocontinuous (n : SimplexCategory) :
    (ι F (op n) ⋙ totalFunctor α).IsCocontinuous
      (J (op n)).toGrothendieck (topology F' J') :=
  isCocontinuous_comp (ι F (op n)) (totalFunctor α)
    (J (op n)).toGrothendieck (topology F J)

/-- The composite `v_n ⋙ ι F' (op n)` is cocontinuous. -/
instance instComponentCompιIsCocontinuous (n : SimplexCategory) :
    ((α.app (op n)).toFunctor ⋙ ι F' (op n)).IsCocontinuous
      (J (op n)).toGrothendieck (topology F' J') :=
  isCocontinuous_comp (α.app (op n)).toFunctor (ι F' (op n))
    (J (op n)).toGrothendieck (J' (op n)).toGrothendieck

/-- The morphism of topoi `h_total : Sh(C_total) ⟶ Sh(C'_total)` presented by
`totalFunctor`. -/
def total : MorphismOfTopoiIn (topology F' J') (topology F J) :=
  (totalFunctor α).morphismOfTopoiInOfCocontinuous (topology F J) (topology F' J')

/-- Inverse image of `total` is cocontinuous sheaf pullback along `v_total`. -/
theorem total_inverseImage :
    (total J J' α).inverseImage =
      (totalFunctor α).sheafPullbackCocontinuous (Type w) (topology F J) (topology F' J') :=
  sorry

/-- Direct image of `total` is cocontinuous sheaf pushforward along `v_total`. -/
theorem total_pushforward :
    (total J J' α).pushforward =
      (totalFunctor α).sheafPushforwardCocontinuous (Type w) (topology F J) (topology F' J') :=
  sorry

/-- Cocontinuous pushforward comparison of the site square `ιCompMap`. -/
def totalFunctor_comp_ι_pushforward (n : SimplexCategory) :
    (ι F (op n)).sheafPushforwardCocontinuous (Type w)
        (J (op n)).toGrothendieck (topology F J) ⋙
      (totalFunctor α).sheafPushforwardCocontinuous (Type w)
        (topology F J) (topology F' J') ≅
      ((α.app (op n)).toFunctor).sheafPushforwardCocontinuous (Type w)
        (J (op n)).toGrothendieck (J' (op n)).toGrothendieck ⋙
      (ι F' (op n)).sheafPushforwardCocontinuous (Type w)
        (J' (op n)).toGrothendieck (topology F' J') :=
  Functor.sheafPushforwardCocontinuousComp'
      (J (op n)).toGrothendieck (topology F J) (topology F' J')
      (ι F (op n)) (totalFunctor α) (totalFunctor_comp_ι α n) ≪≫
    (Functor.sheafPushforwardCocontinuousComp'
      (J (op n)).toGrothendieck (J' (op n)).toGrothendieck (topology F' J')
      ((α.app (op n)).toFunctor) (ι F' (op n)) (Iso.refl _)).symm

/-- Inverse images commute with the degree-`n` morphisms of topoi:
`g_n⁻¹ ∘ h_total⁻¹ ≅ h_n⁻¹ ∘ (g'_n)⁻¹`. -/
def inverseImage_comp (n : SimplexCategory) :
    (total J J' α).inverseImage ⋙ (fiberMorphism F J n).inverseImage ≅
      (fiberMorphism F' J' n).inverseImage ⋙ (topos J J' α n).inverseImage :=
  Adjunction.leftAdjointUniq
    ((Adjunction.comp
        ((totalFunctor α).sheafPullbackCocontinuousAdjunction
          (topology F J) (topology F' J'))
        ((ι F (op n)).sheafPullbackCocontinuousAdjunction
          (J (op n)).toGrothendieck (topology F J))).ofNatIsoRight
      (totalFunctor_comp_ι_pushforward J J' α n))
    (Adjunction.comp
      ((ι F' (op n)).sheafPullbackCocontinuousAdjunction
        (J' (op n)).toGrothendieck (topology F' J'))
      ((α.app (op n)).toFunctor.sheafPullbackCocontinuousAdjunction
        (J (op n)).toGrothendieck (J' (op n)).toGrothendieck))

/-- Mate of the cocontinuous pushforward square `ιCompMap` along `g_n` and `g'_n`. -/
def restrict_pushforward_mate (n : SimplexCategory) :
    (total J J' α).pushforward ⋙ (fiberMorphism F' J' n).inverseImage ⟶
      (fiberMorphism F J n).inverseImage ⋙ (topos J J' α n).pushforward :=
  (mateEquiv (fiberMorphism F J n).adjunction (fiberMorphism F' J' n).adjunction).symm
    (totalFunctor_comp_ι_pushforward J J' α n).hom

/-- The mixed mate of `ιCompMap` is invertible. -/
instance restrict_pushforward_mate_isIso (n : SimplexCategory) :
    IsIso (restrict_pushforward_mate J J' α n) :=
  sorry

/-- The mixed identity `(g'_n)⁻¹ ∘ h_total,* ≅ h_n,* ∘ g_n⁻¹`. -/
def restrict_pushforward (n : SimplexCategory) :
    (total J J' α).pushforward ⋙ (fiberMorphism F' J' n).inverseImage ≅
      (fiberMorphism F J n).inverseImage ⋙ (topos J J' α n).pushforward :=
  asIso (restrict_pushforward_mate J J' α n)

/-- Taking left adjoints of the mixed identity in case B yields
`h_total⁻¹ ∘ (g'_n)^{Sh}_! ≅ g^{Sh}_{n!} ∘ h_n⁻¹`. -/
def lowerShriek_comp (n : SimplexCategory) :
    fiberSheafLowerShriek F' J' n ⋙ (total J J' α).inverseImage ≅
      (topos J J' α n).inverseImage ⋙ fiberSheafLowerShriek F J n :=
  Adjunction.leftAdjointUniq
    ((Adjunction.comp (fiberSheafLowerShriek_adjunction F' J' n)
        ((totalFunctor α).sheafPullbackCocontinuousAdjunction
          (topology F J) (topology F' J'))).ofNatIsoRight
      (Functor.isoWhiskerLeft ((total J J' α).pushforward)
          (fiberInverseImageIso F' J' n).symm ≪≫
        restrict_pushforward J J' α n ≪≫
        Functor.isoWhiskerRight (fiberInverseImageIso F J n)
          (topos J J' α n).pushforward))
    (Adjunction.comp
      ((α.app (op n)).toFunctor.sheafPullbackCocontinuousAdjunction
        (J (op n)).toGrothendieck (J' (op n)).toGrothendieck)
      (fiberSheafLowerShriek_adjunction F J n))

end IsFiberwiseMorphism

end CategoryTheory.Grothendieck

