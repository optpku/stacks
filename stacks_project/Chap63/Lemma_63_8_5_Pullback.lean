/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Whiskering
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import stacks_project.Chap59.Definition_59_77_1
public import stacks_project.Chap59.Lemma_59_80_9_Pullback

/-!
# Inverse image of étale sheaves of modules

Small-étale inverse image `b⁻¹` of sheaves of `Λ`-modules, and the induced
exact functor on unbounded derived categories `D(X_étale, Λ)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry
open CategoryTheory.Sheaf
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Inverse image of small-étale sheaves of `Λ`-modules along a morphism of
schemes. -/
abbrev etaleModuleSheafPullback {A B : Scheme.{u}} (h : A ⟶ B) (Λ : Type u)
    [CommRing Λ]
    [HasWeakSheafify A.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ P : B.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback h).op.HasLeftKanExtension P] :
    Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ) ⥤
      Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ) :=
  (smallEtalePullback h).sheafPullback (ModuleCat.{u} Λ)
    B.smallEtaleTopology A.smallEtaleTopology

/-- Inverse image of module sheaves is sheaf pullback along
`smallEtalePullback`. -/
theorem etaleModuleSheafPullback_eq {A B : Scheme.{u}} (h : A ⟶ B) (Λ : Type u)
    [CommRing Λ]
    [HasWeakSheafify A.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ P : B.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback h).op.HasLeftKanExtension P] :
    etaleModuleSheafPullback h Λ =
      (smallEtalePullback h).sheafPullback (ModuleCat.{u} Λ)
        B.smallEtaleTopology A.smallEtaleTopology :=
  sorry

/-- Inverse image of sheaves of `Λ`-modules is additive. -/
instance etaleModuleSheafPullback_additive {A B : Scheme.{u}} (h : A ⟶ B)
    (Λ : Type u) [CommRing Λ]
    [HasWeakSheafify A.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ P : B.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback h).op.HasLeftKanExtension P]
    [Abelian (Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ))]
    [Abelian (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ))] :
    @Functor.Additive
      (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ))
      (Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ)) _ _
      Abelian.toPreadditive Abelian.toPreadditive
      (etaleModuleSheafPullback h Λ) :=
  sorry

/-- Inverse image of sheaves of `Λ`-modules preserves finite limits. -/
instance etaleModuleSheafPullback_preservesFiniteLimits {A B : Scheme.{u}}
    (h : A ⟶ B) (Λ : Type u) [CommRing Λ]
    [HasWeakSheafify A.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ P : B.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback h).op.HasLeftKanExtension P]
    [Abelian (Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ))]
    [Abelian (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ))] :
    PreservesFiniteLimits (etaleModuleSheafPullback h Λ) :=
  sorry

/-- Inverse image of sheaves of `Λ`-modules preserves finite colimits. -/
instance etaleModuleSheafPullback_preservesFiniteColimits {A B : Scheme.{u}}
    (h : A ⟶ B) (Λ : Type u) [CommRing Λ]
    [HasWeakSheafify A.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ P : B.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback h).op.HasLeftKanExtension P]
    [Abelian (Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ))]
    [Abelian (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ))] :
    PreservesFiniteColimits (etaleModuleSheafPullback h Λ) :=
  sorry

/-- Inverse-image identification along equal morphisms. -/
def etaleModuleSheafPullback_congr {A B : Scheme.{u}} {p q : A ⟶ B}
    (hpq : p = q) (Λ : Type u) [CommRing Λ]
    [HasWeakSheafify A.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ P : B.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback p).op.HasLeftKanExtension P]
    [∀ P : B.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback q).op.HasLeftKanExtension P] :
    etaleModuleSheafPullback p Λ ≅ etaleModuleSheafPullback q Λ :=
  hpq ▸ Iso.refl _

/-- Pullback of module sheaves along a composite is the composite pullback. -/
def etaleModuleSheafPullback_comp {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B)
    (Λ : Type u) [CommRing Λ]
    [HasWeakSheafify B.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasWeakSheafify C.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ P : A.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback p).op.HasLeftKanExtension P]
    [∀ P : B.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback q).op.HasLeftKanExtension P]
    [∀ P : A.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback (q ≫ p)).op.HasLeftKanExtension P] :
    etaleModuleSheafPullback p Λ ⋙ etaleModuleSheafPullback q Λ ≅
      etaleModuleSheafPullback (q ≫ p) Λ :=
  let siteIso :
      smallEtalePullback p ⋙ smallEtalePullback q ≅
        smallEtalePullback (q ≫ p) :=
    (MorphismProperty.Over.pullbackComp q p).symm
  Adjunction.leftAdjointCompIso
    ((smallEtalePullback p).sheafAdjunctionContinuous (ModuleCat.{u} Λ)
      A.smallEtaleTopology B.smallEtaleTopology)
    ((smallEtalePullback q).sheafAdjunctionContinuous (ModuleCat.{u} Λ)
      B.smallEtaleTopology C.smallEtaleTopology)
    ((smallEtalePullback (q ≫ p)).sheafAdjunctionContinuous (ModuleCat.{u} Λ)
      A.smallEtaleTopology C.smallEtaleTopology)
    (sheafPushforwardContinuousComp' siteIso (ModuleCat.{u} Λ)
      A.smallEtaleTopology B.smallEtaleTopology C.smallEtaleTopology)

/-- The inverse-image square of module sheaves associated to a cartesian square
of schemes. -/
def etaleModuleSheafPullback_square {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g) (Λ : Type u) [CommRing Λ]
    [HasWeakSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasWeakSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback g).op.HasLeftKanExtension P]
    [∀ P : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback f').op.HasLeftKanExtension P]
    [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P]
    [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback g').op.HasLeftKanExtension P]
    [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback (f' ≫ g)).op.HasLeftKanExtension P]
    [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback (g' ≫ f)).op.HasLeftKanExtension P] :
    etaleModuleSheafPullback g Λ ⋙ etaleModuleSheafPullback f' Λ ≅
      etaleModuleSheafPullback f Λ ⋙ etaleModuleSheafPullback g' Λ :=
  etaleModuleSheafPullback_comp g f' Λ ≪≫
    etaleModuleSheafPullback_congr h_cart.w.symm Λ ≪≫
    (etaleModuleSheafPullback_comp f g' Λ).symm

/-- Inverse image of module sheaves commutes with forgetting coefficients. -/
def etaleModuleSheafPullback_compSheafComposeIso {A B : Scheme.{u}}
    (h : A ⟶ B) (Λ : Type u) [CommRing Λ]
    [HasWeakSheafify A.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasWeakSheafify A.smallEtaleTopology AddCommGrpCat.{u}]
    [A.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    [B.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    [A.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    [∀ P : B.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback h).op.HasLeftKanExtension P]
    [∀ P : B.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallEtalePullback h).op.HasLeftKanExtension P]
    [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (smallEtalePullback h).op] :
    etaleModuleSheafPullback h Λ ⋙
        sheafCompose A.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) ≅
      sheafCompose B.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) ⋙
        etaleAbelianSheafPullback h :=
  Functor.sheafPullback.compSheafComposeIso (smallEtalePullback h)
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})
    B.smallEtaleTopology A.smallEtaleTopology

/-- Derived inverse image `b⁻¹` on `D(X_étale, Λ)`, induced by the exact
sheaf-level functor `etaleModuleSheafPullback`. -/
def etaleModuleDerivedInverseImage {A B : Scheme.{u}} (h : A ⟶ B) (Λ : Type u)
    [CommRing Λ]
    [HasWeakSheafify A.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasWeakSheafify B.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ P : B.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback h).op.HasLeftKanExtension P]
    [∀ U : A.Etale,
      HasWeakSheafify (A.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
    [∀ U : B.Etale,
      HasWeakSheafify (B.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
    [HasDerivedCategory (Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ))] :
    EtaleDerived B Λ ⥤ EtaleDerived A Λ :=
  (etaleModuleSheafPullback h Λ).mapDerivedCategory

/-- Derived inverse image is `mapDerivedCategory` of module sheaf pullback. -/
theorem etaleModuleDerivedInverseImage_def {A B : Scheme.{u}} (h : A ⟶ B)
    (Λ : Type u) [CommRing Λ]
    [HasWeakSheafify A.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasWeakSheafify B.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ P : B.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback h).op.HasLeftKanExtension P]
    [∀ U : A.Etale,
      HasWeakSheafify (A.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
    [∀ U : B.Etale,
      HasWeakSheafify (B.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
    [HasDerivedCategory (Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ))] :
    etaleModuleDerivedInverseImage h Λ =
      (etaleModuleSheafPullback h Λ).mapDerivedCategory :=
  sorry

/-- Evaluating derived inverse image on an object of `D(B_étale, Λ)`. -/
theorem etaleModuleDerivedInverseImage_obj {A B : Scheme.{u}} (h : A ⟶ B)
    (Λ : Type u) [CommRing Λ]
    [HasWeakSheafify A.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasWeakSheafify B.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ P : B.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback h).op.HasLeftKanExtension P]
    [∀ U : A.Etale,
      HasWeakSheafify (A.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
    [∀ U : B.Etale,
      HasWeakSheafify (B.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
    [HasDerivedCategory (Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ))]
    (K : EtaleDerived B Λ) :
    (etaleModuleDerivedInverseImage h Λ).obj K =
      (etaleModuleSheafPullback h Λ).mapDerivedCategory.obj K :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
