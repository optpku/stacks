module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Right
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import ReasLib.CategoryTheory.Sites.Simplicial.TotalMorphism
public import ReasLib.CategoryTheory.Sites.Simplicial.Injective

/-!
# Derived mixed identity for a morphism of simplicial sites

A morphism of simplicial sites `α : C' ⟶ C` in the covariant presentation induces
abelian direct images `h_total,*` and `h_n,*`. Restriction along `g_n` commutes with
unbounded derived direct image: `(g'_n)⁻¹ ∘ R h_total,* ≅ R h_n,* ∘ g_n⁻¹` on
`D(Ab(C_total))`.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite
open ComplexShape
open scoped CategoryTheory.MorphismOfTopoiIn

noncomputable section

namespace CategoryTheory.SimplicialSites

section Restriction

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]

/-- Restriction of abelian sheaves along `ofStage C n` preserves finite limits. -/
instance stageRestrictAb_preservesFiniteLimits (n : SimplexCategory) :
    PreservesFiniteLimits (stageRestrict C J AddCommGrpCat.{w} n) :=
  sorry

/-- Restriction of abelian sheaves along `ofStage C n` preserves finite colimits. -/
instance stageRestrictAb_preservesFiniteColimits (n : SimplexCategory) :
    PreservesFiniteColimits (stageRestrict C J AddCommGrpCat.{w} n) :=
  sorry

variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasDerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})]
variable [∀ n, HasDerivedCategory (Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w})]

/-- Restriction `g_n⁻¹` on unbounded derived categories of abelian sheaves. -/
abbrev derivedRestrict (n : SimplexCategory) :
    DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}) ⥤
      DerivedCategory (Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w}) :=
  (stageRestrict C J AddCommGrpCat.{w} n).mapDerivedCategory

end Restriction

variable {C C' : SimplexCategory ⥤ Cat.{v, u}}
variable (J : ∀ n, Precoverage (C.obj n)) (J' : ∀ n, Precoverage (C'.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J' n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C'.obj m)ᵒᵖ ⥤ Type w),
    ((C'.map φ).toFunctor).op.HasLeftKanExtension P]
variable [instC : IsMorphismDiagram C J] [instC' : IsMorphismDiagram C' J']
variable (α : C' ⟶ C)
variable [∀ n (P : (C'.obj n)ᵒᵖ ⥤ Type w), ((α.app n).toFunctor).op.HasLeftKanExtension P]
variable [hα : IsMorphism J J' α]
include instC instC' hα

variable [HasWeakSheafify (topology C J) (Type w)]
variable [HasWeakSheafify (topology C' J') (Type w)]
variable [HasSheafify (topology C J) (Type w)]
variable [HasSheafify (topology C' J') (Type w)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasSheafify (J' n).toGrothendieck (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (C'.obj n)ᵒᵖ ⥤ Type w, (ofStage C' n).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (C'.obj n)ᵒᵖ ⥤ Type w, (ofStage C' n).op.HasPointwiseRightKanExtension P]
variable [∀ P : (totalSite C')ᵒᵖ ⥤ Type w, ((IsMorphism.totalFunctor α).op).HasLeftKanExtension P]

variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasSheafify (topology C' J') AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J' n).toGrothendieck AddCommGrpCat.{w}]
variable [HasDerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})]
variable [HasDerivedCategory (Sheaf (topology C' J') AddCommGrpCat.{w})]
variable [∀ n, HasDerivedCategory (Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w})]
variable [∀ n, HasDerivedCategory (Sheaf ((J' n).toGrothendieck) AddCommGrpCat.{w})]
variable [IsGrothendieckAbelian.{max u v} (Sheaf (topology C J) AddCommGrpCat.{w})]
variable [∀ n, IsGrothendieckAbelian.{max u v}
    (Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w})]

namespace IsMorphism

/-- The abelian direct image `h_total,*` of the total topos morphism. -/
abbrev totalPushforwardAb :
    Sheaf (topology C J) AddCommGrpCat.{w} ⥤
      Sheaf (topology C' J') AddCommGrpCat.{w} :=
  (totalFunctor α).sheafPushforwardContinuous AddCommGrpCat.{w}
    (topology C' J') (topology C J)

/-- The abelian direct image `h_n,*` of the degree-`n` morphism of topoi. -/
abbrev pushforwardAb (n : SimplexCategory) :
    Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w} ⥤
      Sheaf ((J' n).toGrothendieck) AddCommGrpCat.{w} :=
  (α.app n).toFunctor.sheafPushforwardContinuous AddCommGrpCat.{w}
    (J' n).toGrothendieck (J n).toGrothendieck

/-- The unbounded derived direct image `R h_total,*`. -/
def derivedTotal :
    DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}) ⥤
      DerivedCategory (Sheaf (topology C' J') AddCommGrpCat.{w}) :=
  Functor.RightDerived.Homotopy.functor
    (totalPushforwardAb J J' α :
      Sheaf (topology C J) AddCommGrpCat.{w} ⥤
        Sheaf (topology C' J') AddCommGrpCat.{w})

/-- Cochain-level unit of `R h_total,*`. -/
def derivedTotal_unit :
    (totalPushforwardAb J J' α).mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q :
          CochainComplex (Sheaf (topology C' J') AddCommGrpCat.{w}) ℤ ⥤
            DerivedCategory (Sheaf (topology C' J') AddCommGrpCat.{w})) ⟶
      (DerivedCategory.Q :
          CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ ⥤
            DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})) ⋙
        derivedTotal J J' α :=
  Functor.RightDerived.Homotopy.cochainUnit
    (totalPushforwardAb J J' α :
      Sheaf (topology C J) AddCommGrpCat.{w} ⥤
        Sheaf (topology C' J') AddCommGrpCat.{w})

/-- The unbounded derived direct image `R h_n,*`. -/
def derivedPushforward (n : SimplexCategory) :
    DerivedCategory (Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w}) ⥤
      DerivedCategory (Sheaf ((J' n).toGrothendieck) AddCommGrpCat.{w}) :=
  Functor.RightDerived.Homotopy.functor
    (pushforwardAb J J' α n :
      Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w} ⥤
        Sheaf ((J' n).toGrothendieck) AddCommGrpCat.{w})

/-- Cochain-level unit of `R h_n,*`. -/
def derivedPushforward_unit (n : SimplexCategory) :
    (pushforwardAb J J' α n).mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q :
          CochainComplex (Sheaf ((J' n).toGrothendieck) AddCommGrpCat.{w}) ℤ ⥤
            DerivedCategory (Sheaf ((J' n).toGrothendieck) AddCommGrpCat.{w})) ⟶
      (DerivedCategory.Q :
          CochainComplex (Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w}) ℤ ⥤
            DerivedCategory (Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w})) ⋙
        derivedPushforward J J' α n :=
  Functor.RightDerived.Homotopy.cochainUnit
    (pushforwardAb J J' α n :
      Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w} ⥤
        Sheaf ((J' n).toGrothendieck) AddCommGrpCat.{w})

/-- Continuous pushforward form of the underived abelian mixed identity:
`h_total,* ⋙ stageRestrict' ≅ stageRestrict ⋙ h_n,*`. -/
def abelianRestrictPushforward (n : SimplexCategory) :
    totalPushforwardAb J J' α ⋙ stageRestrict C' J' AddCommGrpCat.{w} n ≅
      stageRestrict C J AddCommGrpCat.{w} n ⋙ pushforwardAb J J' α n :=
  Functor.sheafPushforwardContinuousComp' (totalFunctor_comp_ofStage α n) AddCommGrpCat.{w}
      (J' n).toGrothendieck (topology C' J') (topology C J) ≪≫
    (Functor.sheafPushforwardContinuousComp ((α.app n).toFunctor) (ofStage C n)
      AddCommGrpCat.{w} (J' n).toGrothendieck (J n).toGrothendieck (topology C J)).symm

/-- Objectwise underived mixed identity on an abelian sheaf. -/
def abelianRestrictPushforward_obj (n : SimplexCategory)
    (K : Sheaf (topology C J) AddCommGrpCat.{w}) :
    (stageRestrict C' J' AddCommGrpCat.{w} n).obj
      ((totalPushforwardAb J J' α).obj K) ≅
      (pushforwardAb J J' α n).obj
        ((stageRestrict C J AddCommGrpCat.{w} n).obj K) :=
  (abelianRestrictPushforward J J' α n).app K

/-- Cochain-level form of the underived abelian mixed identity. -/
def abelianRestrictPushforward_cochain (n : SimplexCategory) :
    (totalPushforwardAb J J' α).mapHomologicalComplex (up ℤ) ⋙
        (stageRestrict C' J' AddCommGrpCat.{w} n).mapHomologicalComplex (up ℤ) ≅
      (stageRestrict C J AddCommGrpCat.{w} n).mapHomologicalComplex (up ℤ) ⋙
        (pushforwardAb J J' α n).mapHomologicalComplex (up ℤ) :=
  (Functor.mapHomologicalComplexCompIso
      (Iso.refl (totalPushforwardAb J J' α ⋙
        stageRestrict C' J' AddCommGrpCat.{w} n)) (up ℤ)).symm ≪≫
    NatIso.mapHomologicalComplex (abelianRestrictPushforward J J' α n) (up ℤ) ≪≫
    Functor.mapHomologicalComplexCompIso
      (Iso.refl (stageRestrict C J AddCommGrpCat.{w} n ⋙ pushforwardAb J J' α n))
      (up ℤ)

/-- Restriction after `R h_total,*` is a right-derived functor of the underived mixed
composite, using that restriction preserves K-injectives. -/
instance restrict_derivedPushforward_isRightDerived (n : SimplexCategory) :
    (derivedTotal J J' α ⋙ derivedRestrict C' J' n).IsRightDerivedFunctor
      ((Functor.associator
            ((stageRestrict C J AddCommGrpCat.{w} n).mapHomologicalComplex (up ℤ))
            ((pushforwardAb J J' α n).mapHomologicalComplex (up ℤ))
            DerivedCategory.Q).inv ≫
        Functor.whiskerRight (abelianRestrictPushforward_cochain J J' α n).inv
          DerivedCategory.Q ≫
          (Functor.associator
                ((totalPushforwardAb J J' α).mapHomologicalComplex (up ℤ))
                ((stageRestrict C' J' AddCommGrpCat.{w} n).mapHomologicalComplex (up ℤ))
                DerivedCategory.Q).hom ≫
            Functor.RightDerived.Composition.iteratedUnit (derivedTotal_unit J J' α)
              (stageRestrict C' J' AddCommGrpCat.{w} n).mapDerivedCategoryFactors.inv)
      (HomologicalComplex.quasiIso (Sheaf (topology C J) AddCommGrpCat.{w}) (up ℤ)) :=
  sorry

/-- Derived mixed comparison `(g'_n)⁻¹ ∘ R h_total,* ⟶ R h_n,* ∘ g_n⁻¹`. -/
def restrict_derivedPushforward_hom (n : SimplexCategory) :
    derivedTotal J J' α ⋙ derivedRestrict C' J' n ⟶
      derivedRestrict C J n ⋙ derivedPushforward J J' α n :=
  Functor.RightDerived.Composition.squareOfIso
    (HomologicalComplex.quasiIso (Sheaf (topology C J) AddCommGrpCat.{w}) (up ℤ))
    (abelianRestrictPushforward_cochain J J' α n)
    (derivedTotal_unit J J' α)
    (stageRestrict C' J' AddCommGrpCat.{w} n).mapDerivedCategoryFactors.inv
    (stageRestrict C J AddCommGrpCat.{w} n).mapDerivedCategoryFactors.inv
    (derivedPushforward_unit J J' α n)

/-- The derived mixed comparison is invertible. -/
instance restrict_derivedPushforward_hom_isIso (n : SimplexCategory) :
    IsIso (restrict_derivedPushforward_hom J J' α n) :=
  sorry

/-- The mixed identity `(g'_n)⁻¹ ∘ R h_total,* ≅ R h_n,* ∘ g_n⁻¹` in `D(Ab(C'_n))`. -/
def restrict_derivedPushforward (n : SimplexCategory) :
    derivedTotal J J' α ⋙ derivedRestrict C' J' n ≅
      derivedRestrict C J n ⋙ derivedPushforward J J' α n :=
  asIso (restrict_derivedPushforward_hom J J' α n)

/-- Objectwise mixed identity `(g'_n)⁻¹ R h_total,* K ≅ R h_n,* g_n⁻¹ K`. -/
def restrict_derivedPushforward_obj (n : SimplexCategory)
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})) :
    (derivedRestrict C' J' n).obj ((derivedTotal J J' α).obj K) ≅
      (derivedPushforward J J' α n).obj ((derivedRestrict C J n).obj K) :=
  (restrict_derivedPushforward J J' α n).app K

end IsMorphism

end CategoryTheory.SimplicialSites
