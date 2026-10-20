/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Mates
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Right
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import ReasLib.CategoryTheory.Sites.Grothendieck.SimplicialTotalMorphism
public import ReasLib.CategoryTheory.Sites.Grothendieck.Injective

/-!
# Derived mixed identity for a fiberwise morphism of simplicial sites

A morphism of simplicial sites `α : F ⟶ F'` in the fiberwise presentation induces
abelian direct images `h_total,*` and `h_n,*` as cocontinuous pushforwards. Restriction
along `g_n` commutes with unbounded derived direct image:
`(g'_n)⁻¹ ∘ R h_total,* ≅ R h_n,* ∘ g_n⁻¹` on `D(Ab(C_total))`.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open ComplexShape
open scoped CategoryTheory.MorphismOfTopoiIn

noncomputable section

namespace CategoryTheory.Grothendieck

section Restriction

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]

/-- Restriction of abelian sheaves along `ι F (op n)` preserves finite limits. -/
instance fiberRestrictAb_preservesFiniteLimits (n : SimplexCategory) :
    PreservesFiniteLimits (fiberRestrict F J AddCommGrpCat.{w} n) :=
  sorry

/-- Restriction of abelian sheaves along `ι F (op n)` preserves finite colimits. -/
instance fiberRestrictAb_preservesFiniteColimits (n : SimplexCategory) :
    PreservesFiniteColimits (fiberRestrict F J AddCommGrpCat.{w} n) :=
  sorry

variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J (op n)).toGrothendieck AddCommGrpCat.{w}]
variable [HasDerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w})]
variable [∀ n, HasDerivedCategory (Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w})]

/-- Restriction `g_n⁻¹` on unbounded derived categories of abelian sheaves. -/
abbrev derivedRestrict (n : SimplexCategory) :
    DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}) ⥤
      DerivedCategory (Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w}) :=
  (fiberRestrict F J AddCommGrpCat.{w} n).mapDerivedCategory

end Restriction

variable {F F' : SimplicialObject Cat.{v, u}}
variable (J : ∀ n, Precoverage (F.obj n)) (J' : ∀ n, Precoverage (F'.obj n))
variable [instF : IsFiberwiseSite F J] [instF' : IsFiberwiseSite F' J']
variable (α : F ⟶ F')
variable [hα : IsFiberwiseMorphism J J' α]
include instF instF' hα

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
variable [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
    (Grothendieck.map α).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    ((α.app (op n)).toFunctor ⋙ ι F' (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n) ⋙ Grothendieck.map α).op.HasPointwiseRightKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J' n).toGrothendieck (Type w)]

variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [HasSheafify (topology F' J') AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J' n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F'.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι F' (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n (P : (F.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((α.app n).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ P : (Grothendieck F)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (Grothendieck.map α).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    ((α.app (op n)).toFunctor ⋙ ι F' (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι F (op n) ⋙ Grothendieck.map α).op.HasPointwiseRightKanExtension P]
variable [HasDerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w})]
variable [HasDerivedCategory (Sheaf (topology F' J') AddCommGrpCat.{w})]
variable [∀ n, HasDerivedCategory (Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w})]
variable [∀ n, HasDerivedCategory (Sheaf ((J' (op n)).toGrothendieck) AddCommGrpCat.{w})]
variable [IsGrothendieckAbelian.{max u v} (Sheaf (topology F J) AddCommGrpCat.{w})]
variable [∀ n, IsGrothendieckAbelian.{max u v}
    (Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w})]

namespace IsFiberwiseMorphism

/-- The abelian direct image `h_total,*` of the total topos morphism. -/
abbrev totalPushforwardAb :
    Sheaf (topology F J) AddCommGrpCat.{w} ⥤
      Sheaf (topology F' J') AddCommGrpCat.{w} :=
  (Grothendieck.map α).sheafPushforwardCocontinuous AddCommGrpCat.{w}
    (topology F J) (topology F' J')

/-- The abelian direct image `h_n,*` of the degree-`n` morphism of topoi. -/
abbrev pushforwardAb (n : SimplexCategory) :
    Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w} ⥤
      Sheaf ((J' (op n)).toGrothendieck) AddCommGrpCat.{w} :=
  (α.app (op n)).toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{w}
    (J (op n)).toGrothendieck (J' (op n)).toGrothendieck

/-- Abelian total direct image is additive. -/
instance totalPushforwardAb_additive :
    (totalPushforwardAb J J' α).Additive :=
  sorry

/-- Abelian degree-`n` direct image is additive. -/
instance pushforwardAb_additive (n : SimplexCategory) :
    (pushforwardAb J J' α n).Additive :=
  sorry

/-- Cocontinuous pushforward comparison of the site square `ιCompMap` on abelian sheaves. -/
def totalFunctor_comp_ι_pushforwardAb (n : SimplexCategory) :
    (ι F (op n)).sheafPushforwardCocontinuous AddCommGrpCat.{w}
        (J (op n)).toGrothendieck (topology F J) ⋙
      (Grothendieck.map α).sheafPushforwardCocontinuous AddCommGrpCat.{w}
        (topology F J) (topology F' J') ≅
      ((α.app (op n)).toFunctor).sheafPushforwardCocontinuous AddCommGrpCat.{w}
        (J (op n)).toGrothendieck (J' (op n)).toGrothendieck ⋙
      (ι F' (op n)).sheafPushforwardCocontinuous AddCommGrpCat.{w}
        (J' (op n)).toGrothendieck (topology F' J') :=
  Functor.sheafPushforwardCocontinuousComp'
      (J (op n)).toGrothendieck (topology F J) (topology F' J')
      (ι F (op n)) (Grothendieck.map α) (Grothendieck.ιCompMap α (op n)) ≪≫
    (Functor.sheafPushforwardCocontinuousComp'
      (J (op n)).toGrothendieck (J' (op n)).toGrothendieck (topology F' J')
      ((α.app (op n)).toFunctor) (ι F' (op n)) (Iso.refl _)).symm

/-- Mate of the cocontinuous abelian pushforward square along `g_n` and `g'_n`. -/
def abelianRestrictPushforward_hom (n : SimplexCategory) :
    totalPushforwardAb J J' α ⋙ fiberRestrict F' J' AddCommGrpCat.{w} n ⟶
      fiberRestrict F J AddCommGrpCat.{w} n ⋙ pushforwardAb J J' α n :=
  (mateEquiv
      ((ι F (op n)).sheafAdjunctionCocontinuous AddCommGrpCat.{w}
        (J (op n)).toGrothendieck (topology F J))
      ((ι F' (op n)).sheafAdjunctionCocontinuous AddCommGrpCat.{w}
        (J' (op n)).toGrothendieck (topology F' J'))).symm
    (totalFunctor_comp_ι_pushforwardAb J J' α n).hom

/-- The mixed mate of the abelian `ιCompMap` square is invertible. -/
instance abelianRestrictPushforward_hom_isIso (n : SimplexCategory) :
    IsIso (abelianRestrictPushforward_hom J J' α n) :=
  sorry

/-- The underived abelian mixed identity `(g'_n)⁻¹ ∘ h_total,* ≅ h_n,* ∘ g_n⁻¹`. -/
def abelianRestrictPushforward (n : SimplexCategory) :
    totalPushforwardAb J J' α ⋙ fiberRestrict F' J' AddCommGrpCat.{w} n ≅
      fiberRestrict F J AddCommGrpCat.{w} n ⋙ pushforwardAb J J' α n :=
  asIso (abelianRestrictPushforward_hom J J' α n)

/-- Objectwise underived mixed identity on an abelian sheaf. -/
def abelianRestrictPushforward_obj (n : SimplexCategory)
    (K : Sheaf (topology F J) AddCommGrpCat.{w}) :
    (fiberRestrict F' J' AddCommGrpCat.{w} n).obj
      ((totalPushforwardAb J J' α).obj K) ≅
      (pushforwardAb J J' α n).obj
        ((fiberRestrict F J AddCommGrpCat.{w} n).obj K) :=
  (abelianRestrictPushforward J J' α n).app K

/-- Cochain-level form of the underived abelian mixed identity. -/
def abelianRestrictPushforward_cochain (n : SimplexCategory) :
    (totalPushforwardAb J J' α).mapHomologicalComplex (up ℤ) ⋙
        (fiberRestrict F' J' AddCommGrpCat.{w} n).mapHomologicalComplex (up ℤ) ≅
      (fiberRestrict F J AddCommGrpCat.{w} n).mapHomologicalComplex (up ℤ) ⋙
        (pushforwardAb J J' α n).mapHomologicalComplex (up ℤ) :=
  (Functor.mapHomologicalComplexCompIso
      (Iso.refl (totalPushforwardAb J J' α ⋙
        fiberRestrict F' J' AddCommGrpCat.{w} n)) (up ℤ)).symm ≪≫
    NatIso.mapHomologicalComplex (abelianRestrictPushforward J J' α n) (up ℤ) ≪≫
    Functor.mapHomologicalComplexCompIso
      (Iso.refl (fiberRestrict F J AddCommGrpCat.{w} n ⋙ pushforwardAb J J' α n))
      (up ℤ)

/-- The unbounded derived direct image `R h_total,*`. -/
def derivedTotal :
    DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}) ⥤
      DerivedCategory (Sheaf (topology F' J') AddCommGrpCat.{w}) :=
  Functor.RightDerived.Homotopy.functor
    (totalPushforwardAb J J' α :
      Sheaf (topology F J) AddCommGrpCat.{w} ⥤
        Sheaf (topology F' J') AddCommGrpCat.{w})

/-- Cochain-level unit of `R h_total,*`. -/
def derivedTotal_unit :
    (totalPushforwardAb J J' α).mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q :
          CochainComplex (Sheaf (topology F' J') AddCommGrpCat.{w}) ℤ ⥤
            DerivedCategory (Sheaf (topology F' J') AddCommGrpCat.{w})) ⟶
      (DerivedCategory.Q :
          CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ ⥤
            DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w})) ⋙
        derivedTotal J J' α :=
  Functor.RightDerived.Homotopy.cochainUnit
    (totalPushforwardAb J J' α :
      Sheaf (topology F J) AddCommGrpCat.{w} ⥤
        Sheaf (topology F' J') AddCommGrpCat.{w})

/-- The unbounded derived direct image `R h_n,*`. -/
def derivedPushforward (n : SimplexCategory) :
    DerivedCategory (Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w}) ⥤
      DerivedCategory (Sheaf ((J' (op n)).toGrothendieck) AddCommGrpCat.{w}) :=
  Functor.RightDerived.Homotopy.functor
    (pushforwardAb J J' α n :
      Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w} ⥤
        Sheaf ((J' (op n)).toGrothendieck) AddCommGrpCat.{w})

/-- Cochain-level unit of `R h_n,*`. -/
def derivedPushforward_unit (n : SimplexCategory) :
    (pushforwardAb J J' α n).mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q :
          CochainComplex (Sheaf ((J' (op n)).toGrothendieck) AddCommGrpCat.{w}) ℤ ⥤
            DerivedCategory (Sheaf ((J' (op n)).toGrothendieck) AddCommGrpCat.{w})) ⟶
      (DerivedCategory.Q :
          CochainComplex (Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w}) ℤ ⥤
            DerivedCategory (Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w})) ⋙
        derivedPushforward J J' α n :=
  Functor.RightDerived.Homotopy.cochainUnit
    (pushforwardAb J J' α n :
      Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w} ⥤
        Sheaf ((J' (op n)).toGrothendieck) AddCommGrpCat.{w})

/-- Restriction after `R h_total,*` is a right-derived functor of the underived mixed
composite. -/
instance restrict_derivedPushforward_isRightDerived (n : SimplexCategory) :
    (derivedTotal J J' α ⋙ derivedRestrict F' J' n).IsRightDerivedFunctor
      ((Functor.associator
            ((fiberRestrict F J AddCommGrpCat.{w} n).mapHomologicalComplex (up ℤ))
            ((pushforwardAb J J' α n).mapHomologicalComplex (up ℤ))
            DerivedCategory.Q).inv ≫
        Functor.whiskerRight (abelianRestrictPushforward_cochain J J' α n).inv
          DerivedCategory.Q ≫
          (Functor.associator
                ((totalPushforwardAb J J' α).mapHomologicalComplex (up ℤ))
                ((fiberRestrict F' J' AddCommGrpCat.{w} n).mapHomologicalComplex (up ℤ))
                DerivedCategory.Q).hom ≫
            Functor.RightDerived.Composition.iteratedUnit (derivedTotal_unit J J' α)
              (fiberRestrict F' J' AddCommGrpCat.{w} n).mapDerivedCategoryFactors.inv)
      (HomologicalComplex.quasiIso (Sheaf (topology F J) AddCommGrpCat.{w}) (up ℤ)) :=
  sorry

/-- Derived mixed comparison `(g'_n)⁻¹ ∘ R h_total,* ⟶ R h_n,* ∘ g_n⁻¹`. -/
def restrict_derivedPushforward_hom (n : SimplexCategory) :
    derivedTotal J J' α ⋙ derivedRestrict F' J' n ⟶
      derivedRestrict F J n ⋙ derivedPushforward J J' α n :=
  Functor.RightDerived.Composition.squareOfIso
    (HomologicalComplex.quasiIso (Sheaf (topology F J) AddCommGrpCat.{w}) (up ℤ))
    (abelianRestrictPushforward_cochain J J' α n)
    (derivedTotal_unit J J' α)
    (fiberRestrict F' J' AddCommGrpCat.{w} n).mapDerivedCategoryFactors.inv
    (fiberRestrict F J AddCommGrpCat.{w} n).mapDerivedCategoryFactors.inv
    (derivedPushforward_unit J J' α n)

/-- The derived mixed comparison is invertible. -/
instance restrict_derivedPushforward_hom_isIso (n : SimplexCategory) :
    IsIso (restrict_derivedPushforward_hom J J' α n) :=
  sorry

/-- The mixed identity `(g'_n)⁻¹ ∘ R h_total,* ≅ R h_n,* ∘ g_n⁻¹`. -/
def restrict_derivedPushforward (n : SimplexCategory) :
    derivedTotal J J' α ⋙ derivedRestrict F' J' n ≅
      derivedRestrict F J n ⋙ derivedPushforward J J' α n :=
  asIso (restrict_derivedPushforward_hom J J' α n)

/-- Objectwise mixed identity `(g'_n)⁻¹ R h_total,* K ≅ R h_n,* g_n⁻¹ K`. -/
def restrict_derivedPushforward_obj (n : SimplexCategory)
    (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w})) :
    (derivedRestrict F' J' n).obj ((derivedTotal J J' α).obj K) ≅
      (derivedPushforward J J' α n).obj ((derivedRestrict F J n).obj K) :=
  (restrict_derivedPushforward J J' α n).app K

end IsFiberwiseMorphism

end CategoryTheory.Grothendieck
