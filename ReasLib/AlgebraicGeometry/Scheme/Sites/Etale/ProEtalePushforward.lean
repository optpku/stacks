/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.Adjunction.Derived.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Square
public import ReasLib.CategoryTheory.Functor.Exactness.Composition
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.ModulePullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProEtaleComparison

/-!
# Étale-to-pro-étale pushforward comparison

The commutative square of small sites induced by a scheme morphism `f : X ⟶ Y`,
the inverse-image identification `ε⁻¹ ∘ f_étale⁻¹ ≅ f_proétale⁻¹ ∘ ε⁻¹`, and the
canonical Sites/mate arrows `ε⁻¹ ∘ f_* ⟶ f_* ∘ ε⁻¹` on sheaves of sets and on
`D⁺` of abelian sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProEt

noncomputable section

universe u u₁ v₁

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

/-- Underlying scheme of the two paths around the étale/pro-étale site square. -/
def etaleToProEt_baseChangeIso_app_left (f : X ⟶ Y) (U : Y.Etale) :
    ((etaleToProEt Y ⋙ baseChange f).obj U).left ≅
      ((smallEtalePullback f ⋙ etaleToProEt X).obj U).left :=
  Iso.refl _

/-- The underlying comparison of `etaleToProEt_baseChangeIso_app_left` respects structure
morphisms to `X`. -/
theorem etaleToProEt_baseChangeIso_app_w (f : X ⟶ Y) (U : Y.Etale) :
    (etaleToProEt_baseChangeIso_app_left f U).hom ≫
        ((smallEtalePullback f ⋙ etaleToProEt X).obj U).hom =
      ((etaleToProEt Y ⋙ baseChange f).obj U).hom :=
  sorry

/-- Component of the étale/pro-étale site square at an étale object over `Y`. -/
def etaleToProEt_baseChangeIso_app (f : X ⟶ Y) (U : Y.Etale) :
    (etaleToProEt Y ⋙ baseChange f).obj U ≅
      (smallEtalePullback f ⋙ etaleToProEt X).obj U :=
  MorphismProperty.Over.isoMk (etaleToProEt_baseChangeIso_app_left f U)
    (etaleToProEt_baseChangeIso_app_w f U)

/-- Naturality of the components of the étale/pro-étale site square. -/
theorem etaleToProEt_baseChangeIso_naturality (f : X ⟶ Y) {U V : Y.Etale} (g : U ⟶ V) :
    (etaleToProEt Y ⋙ baseChange f).map g ≫
        (etaleToProEt_baseChangeIso_app f V).hom =
      (etaleToProEt_baseChangeIso_app f U).hom ≫
        (smallEtalePullback f ⋙ etaleToProEt X).map g :=
  sorry

/-- Site-level square `ε_Y ⋙ f_proétale ≅ f_étale ⋙ ε_X`. -/
def etaleToProEt_baseChangeIso (f : X ⟶ Y) :
    etaleToProEt Y ⋙ baseChange f ≅ smallEtalePullback f ⋙ etaleToProEt X :=
  NatIso.ofComponents (etaleToProEt_baseChangeIso_app f)
    (etaleToProEt_baseChangeIso_naturality f)

/-- The left component of the site-square isomorphism is the chosen pullback comparison. -/
theorem etaleToProEt_baseChangeIso_hom_app_left (f : X ⟶ Y) (U : Y.Etale) :
    ((etaleToProEt_baseChangeIso f).hom.app U).left =
      (etaleToProEt_baseChangeIso_app_left f U).hom :=
  sorry

/-- The composite `ε_Y ⋙ f_proétale` is continuous. -/
instance etaleToProEt_comp_baseChange_isContinuous (f : X ⟶ Y) :
    Functor.IsContinuous (etaleToProEt Y ⋙ baseChange f)
      Y.smallEtaleTopology (topology X) :=
  Functor.isContinuous_comp (etaleToProEt Y) (baseChange f)
    Y.smallEtaleTopology (topology Y) (topology X)

/-- The composite `f_étale ⋙ ε_X` is continuous. -/
instance smallEtalePullback_comp_etaleToProEt_isContinuous (f : X ⟶ Y) :
    Functor.IsContinuous (smallEtalePullback f ⋙ etaleToProEt X)
      Y.smallEtaleTopology (topology X) :=
  Functor.isContinuous_comp (smallEtalePullback f) (etaleToProEt X)
    Y.smallEtaleTopology X.smallEtaleTopology (topology X)

section Coefficients

variable (A : Type u₁) [Category.{v₁} A]
variable (f : X ⟶ Y)
variable [∀ F : Y.Etaleᵒᵖ ⥤ A, (etaleToProEt Y).op.HasLeftKanExtension F]
variable [∀ F : X.Etaleᵒᵖ ⥤ A, (etaleToProEt X).op.HasLeftKanExtension F]
variable [∀ F : Y.Etaleᵒᵖ ⥤ A, (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ F : Y.ProEtᵒᵖ ⥤ A, (baseChange f).op.HasLeftKanExtension F]
variable [HasWeakSheafify X.smallEtaleTopology A]
variable [HasWeakSheafify (topology X) A] [HasWeakSheafify (topology Y) A]

/-- Direct image of coefficient-`A` sheaves along `f_étale`. -/
abbrev smallEtaleSheafPushforward :
    Sheaf X.smallEtaleTopology A ⥤ Sheaf Y.smallEtaleTopology A :=
  (smallEtalePullback f).sheafPushforwardContinuous A
    Y.smallEtaleTopology X.smallEtaleTopology

/-- `smallEtaleSheafPushforward` is continuous sheaf pushforward along `smallEtalePullback`. -/
theorem smallEtaleSheafPushforward_def :
    smallEtaleSheafPushforward A f =
      (smallEtalePullback f).sheafPushforwardContinuous A
        Y.smallEtaleTopology X.smallEtaleTopology :=
  sorry

/-- Inverse image of coefficient-`A` sheaves along `f_étale`. -/
abbrev smallEtaleSheafPullback :
    Sheaf Y.smallEtaleTopology A ⥤ Sheaf X.smallEtaleTopology A :=
  (smallEtalePullback f).sheafPullback A
    Y.smallEtaleTopology X.smallEtaleTopology

/-- `smallEtaleSheafPullback` is sheaf pullback along `smallEtalePullback`. -/
theorem smallEtaleSheafPullback_def :
    smallEtaleSheafPullback A f =
      (smallEtalePullback f).sheafPullback A
        Y.smallEtaleTopology X.smallEtaleTopology :=
  sorry

/-- Direct image of coefficient-`A` sheaves along `f_proétale`. -/
abbrev proEtSheafPushforward :
    Sheaf (topology X) A ⥤ Sheaf (topology Y) A :=
  (baseChange f).sheafPushforwardContinuous A (topology Y) (topology X)

/-- `proEtSheafPushforward` is continuous sheaf pushforward along `baseChange`. -/
theorem proEtSheafPushforward_def :
    proEtSheafPushforward A f =
      (baseChange f).sheafPushforwardContinuous A (topology Y) (topology X) :=
  sorry

/-- Inverse image of coefficient-`A` sheaves along `f_proétale`. -/
abbrev proEtSheafPullback :
    Sheaf (topology Y) A ⥤ Sheaf (topology X) A :=
  (baseChange f).sheafPullback A (topology Y) (topology X)

/-- `proEtSheafPullback` is sheaf pullback along `baseChange`. -/
theorem proEtSheafPullback_def :
    proEtSheafPullback A f =
      (baseChange f).sheafPullback A (topology Y) (topology X) :=
  sorry

/-- Pushforward square of the étale/pro-étale site comparison, identifying
`ε_{Y,*} ∘ f_proétale,* ≅ f_étale,* ∘ ε_{X,*}`. -/
def etaleToProEt_sheafPushforwardIso :
    proEtSheafPushforward A f ⋙ etaleToProEtSheaf Y A ≅
      etaleToProEtSheaf X A ⋙ smallEtaleSheafPushforward A f :=
  Functor.sheafPushforwardContinuousComp' (etaleToProEt_baseChangeIso f) A
      Y.smallEtaleTopology (topology Y) (topology X) ≪≫
    (Functor.sheafPushforwardContinuousComp'
      (Iso.refl (smallEtalePullback f ⋙ etaleToProEt X)) A
      Y.smallEtaleTopology X.smallEtaleTopology (topology X)).symm

/-- Inverse-image identification `f_étale⁻¹ ⋙ ε_X⁻¹ ≅ ε_Y⁻¹ ⋙ f_proétale⁻¹`. -/
def etaleToProEt_inverseImageIso :
    smallEtaleSheafPullback A f ⋙ etaleToProEtPullback X A ≅
      etaleToProEtPullback Y A ⋙ proEtSheafPullback A f :=
  (Adjunction.leftAdjointCompIso
      (etaleToProEt_sheafAdjunction Y A)
      ((baseChange f).sheafAdjunctionContinuous A (topology Y) (topology X))
      (((smallEtalePullback f).sheafAdjunctionContinuous A
          Y.smallEtaleTopology X.smallEtaleTopology).comp
        (etaleToProEt_sheafAdjunction X A))
      (etaleToProEt_sheafPushforwardIso A f)).symm

/-- `etaleToProEt_inverseImageIso` is the left-adjoint conjugate of the pushforward square. -/
theorem etaleToProEt_inverseImageIso_def :
    etaleToProEt_inverseImageIso A f =
      (Adjunction.leftAdjointCompIso
          (etaleToProEt_sheafAdjunction Y A)
          ((baseChange f).sheafAdjunctionContinuous A (topology Y) (topology X))
          (((smallEtalePullback f).sheafAdjunctionContinuous A
              Y.smallEtaleTopology X.smallEtaleTopology).comp
            (etaleToProEt_sheafAdjunction X A))
          (etaleToProEt_sheafPushforwardIso A f)).symm :=
  sorry

/-- Canonical underived mate `ε_Y⁻¹ ∘ f_étale,* ⟶ f_proétale,* ∘ ε_X⁻¹`. -/
def etaleToProEt_pushforwardHom :
    smallEtaleSheafPushforward A f ⋙ etaleToProEtPullback Y A ⟶
      etaleToProEtPullback X A ⋙ proEtSheafPushforward A f :=
  DerivedBaseChange.map
    ((smallEtalePullback f).sheafAdjunctionContinuous A
      Y.smallEtaleTopology X.smallEtaleTopology)
    ((baseChange f).sheafAdjunctionContinuous A (topology Y) (topology X))
    (etaleToProEt_inverseImageIso A f).symm

/-- `etaleToProEt_pushforwardHom` is the right mate of the inverse-image square. -/
theorem etaleToProEt_pushforwardHom_spec :
    DerivedBaseChange.IsMap
      ((smallEtalePullback f).sheafAdjunctionContinuous A
        Y.smallEtaleTopology X.smallEtaleTopology)
      ((baseChange f).sheafAdjunctionContinuous A (topology Y) (topology X))
      (etaleToProEt_inverseImageIso A f).symm
      (etaleToProEt_pushforwardHom A f) :=
  sorry

/-- Component of the underived mate at a sheaf `F`. -/
theorem etaleToProEt_pushforwardHom_app (F : Sheaf X.smallEtaleTopology A) :
    (etaleToProEt_pushforwardHom A f).app F =
      DerivedBaseChange.app
        ((smallEtalePullback f).sheafAdjunctionContinuous A
          Y.smallEtaleTopology X.smallEtaleTopology)
        ((baseChange f).sheafAdjunctionContinuous A (topology Y) (topology X))
        (etaleToProEt_inverseImageIso A f).symm F :=
  sorry

end Coefficients

section Abelian

variable (f : X ⟶ Y)
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasSheafify (topology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (topology Y) AddCommGrpCat.{u + 1}]
variable [∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
  (etaleToProEt Y).op.HasLeftKanExtension F]
variable [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
  (etaleToProEt X).op.HasLeftKanExtension F]
variable [∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
  (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ F : Y.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
  (baseChange f).op.HasLeftKanExtension F]

/-- Inverse image of abelian sheaves along `ε` preserves finite limits. -/
instance etaleToProEtPullback_preservesFiniteLimits (Z : Scheme.{u})
    [∀ F : Z.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (etaleToProEt Z).op.HasLeftKanExtension F]
    [HasWeakSheafify (topology Z) AddCommGrpCat.{u + 1}] :
    PreservesFiniteLimits (etaleToProEtPullback Z AddCommGrpCat.{u + 1}) :=
  sorry

/-- Inverse image of abelian sheaves along `ε` preserves finite colimits. -/
instance etaleToProEtPullback_preservesFiniteColimits (Z : Scheme.{u})
    [∀ F : Z.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (etaleToProEt Z).op.HasLeftKanExtension F]
    [HasWeakSheafify (topology Z) AddCommGrpCat.{u + 1}] :
    PreservesFiniteColimits (etaleToProEtPullback Z AddCommGrpCat.{u + 1}) :=
  sorry

/-- Inverse image of abelian sheaves along `f_étale` preserves finite limits. -/
instance smallEtaleSheafPullback_preservesFiniteLimits :
    PreservesFiniteLimits (smallEtaleSheafPullback AddCommGrpCat.{u + 1} f) :=
  sorry

/-- Inverse image of abelian sheaves along `f_étale` preserves finite colimits. -/
instance smallEtaleSheafPullback_preservesFiniteColimits :
    PreservesFiniteColimits (smallEtaleSheafPullback AddCommGrpCat.{u + 1} f) :=
  sorry

/-- Inverse image of abelian sheaves along `f_proétale` preserves finite limits. -/
instance proEtSheafPullback_preservesFiniteLimits :
    PreservesFiniteLimits (proEtSheafPullback AddCommGrpCat.{u + 1} f) :=
  sorry

/-- Inverse image of abelian sheaves along `f_proétale` preserves finite colimits. -/
instance proEtSheafPullback_preservesFiniteColimits :
    PreservesFiniteColimits (proEtSheafPullback AddCommGrpCat.{u + 1} f) :=
  sorry

/-- The bounded-below right-derived functor of abelian `f_étale,*` exists. -/
instance smallEtaleSheafPushforward_hasRightDerivedFunctor :
    (smallEtaleSheafPushforward AddCommGrpCat.{u + 1} f).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :=
  sorry

/-- The bounded-below right-derived functor of abelian `f_proétale,*` exists. -/
instance proEtSheafPushforward_hasRightDerivedFunctor :
    (proEtSheafPushforward AddCommGrpCat.{u + 1} f).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (topology X) AddCommGrpCat.{u + 1})) :=
  sorry

/-- Exact inverse image `ε⁻¹` of abelian sheaves. -/
abbrev etaleToProEtPullbackExact (Z : Scheme.{u})
    [∀ F : Z.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (etaleToProEt Z).op.HasLeftKanExtension F]
    [HasWeakSheafify (topology Z) AddCommGrpCat.{u + 1}] :
    Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ₑ
      Sheaf (topology Z) AddCommGrpCat.{u + 1} :=
  ExactFunctor.of (etaleToProEtPullback Z AddCommGrpCat.{u + 1})

/-- `etaleToProEtPullbackExact` is `ExactFunctor.of` of `etaleToProEtPullback`. -/
theorem etaleToProEtPullbackExact_def (Z : Scheme.{u})
    [∀ F : Z.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (etaleToProEt Z).op.HasLeftKanExtension F]
    [HasWeakSheafify (topology Z) AddCommGrpCat.{u + 1}] :
    etaleToProEtPullbackExact Z =
      ExactFunctor.of (etaleToProEtPullback Z AddCommGrpCat.{u + 1}) :=
  sorry

/-- Exact inverse image of abelian sheaves along `f_étale`. -/
abbrev smallEtaleSheafPullbackExact :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ₑ
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  ExactFunctor.of (smallEtaleSheafPullback AddCommGrpCat.{u + 1} f)

/-- `smallEtaleSheafPullbackExact` is `ExactFunctor.of` of `smallEtaleSheafPullback`. -/
theorem smallEtaleSheafPullbackExact_def :
    smallEtaleSheafPullbackExact f =
      ExactFunctor.of (smallEtaleSheafPullback AddCommGrpCat.{u + 1} f) :=
  sorry

/-- Exact inverse image of abelian sheaves along `f_proétale`. -/
abbrev proEtSheafPullbackExact :
    Sheaf (topology Y) AddCommGrpCat.{u + 1} ⥤ₑ
      Sheaf (topology X) AddCommGrpCat.{u + 1} :=
  ExactFunctor.of (proEtSheafPullback AddCommGrpCat.{u + 1} f)

/-- `proEtSheafPullbackExact` is `ExactFunctor.of` of `proEtSheafPullback`. -/
theorem proEtSheafPullbackExact_def :
    proEtSheafPullbackExact f =
      ExactFunctor.of (proEtSheafPullback AddCommGrpCat.{u + 1} f) :=
  sorry

/-- Inverse-image square on exact abelian sheaf functors. -/
def etaleToProEt_inverseImageExactIso :
    (smallEtaleSheafPullbackExact f).comp (etaleToProEtPullbackExact X) ≅
      (etaleToProEtPullbackExact Y).comp (proEtSheafPullbackExact f) :=
  (exactFunctor
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
      (Sheaf (topology X) AddCommGrpCat.{u + 1})).isoMk
    (etaleToProEt_inverseImageIso AddCommGrpCat.{u + 1} f)

/-- Inverse-image square on `D⁺` of abelian sheaves. -/
def etaleToProEt_derivedInverseImageIso :
    ExactFunctor.Derived.Plus.functor (smallEtaleSheafPullbackExact f) ⋙
        ExactFunctor.Derived.Plus.functor (etaleToProEtPullbackExact X) ≅
      ExactFunctor.Derived.Plus.functor (etaleToProEtPullbackExact Y) ⋙
        ExactFunctor.Derived.Plus.functor (proEtSheafPullbackExact f) :=
  ExactFunctor.Derived.Plus.squareIso
    (smallEtaleSheafPullbackExact f) (etaleToProEtPullbackExact X)
    (etaleToProEtPullbackExact Y) (proEtSheafPullbackExact f)
    (etaleToProEt_inverseImageExactIso f)

/-- Canonical `D⁺` mate `ε_Y⁻¹ ∘ Rf_étale,* ⟶ Rf_proétale,* ∘ ε_X⁻¹`. -/
def etaleToProEt_derivedPushforwardHomNat :
    Adjunction.Derived.Plus.right
          (smallEtaleSheafPushforward AddCommGrpCat.{u + 1} f) ⋙
        ExactFunctor.Derived.Plus.functor (etaleToProEtPullbackExact Y) ⟶
      ExactFunctor.Derived.Plus.functor (etaleToProEtPullbackExact X) ⋙
        Adjunction.Derived.Plus.right
          (proEtSheafPushforward AddCommGrpCat.{u + 1} f) :=
  DerivedBaseChange.map
    (Adjunction.Derived.Plus.adjunction (smallEtaleSheafPullbackExact f)
      (smallEtaleSheafPushforward AddCommGrpCat.{u + 1} f)
      ((smallEtalePullback f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
        Y.smallEtaleTopology X.smallEtaleTopology))
    (Adjunction.Derived.Plus.adjunction (proEtSheafPullbackExact f)
      (proEtSheafPushforward AddCommGrpCat.{u + 1} f)
      ((baseChange f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
        (topology Y) (topology X)))
    (etaleToProEt_derivedInverseImageIso f).symm

/-- `etaleToProEt_derivedPushforwardHomNat` is the right mate of the `D⁺` inverse-image square. -/
theorem etaleToProEt_derivedPushforwardHomNat_spec :
    DerivedBaseChange.IsMap
      (Adjunction.Derived.Plus.adjunction (smallEtaleSheafPullbackExact f)
        (smallEtaleSheafPushforward AddCommGrpCat.{u + 1} f)
        ((smallEtalePullback f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
          Y.smallEtaleTopology X.smallEtaleTopology))
      (Adjunction.Derived.Plus.adjunction (proEtSheafPullbackExact f)
        (proEtSheafPushforward AddCommGrpCat.{u + 1} f)
        ((baseChange f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
          (topology Y) (topology X)))
      (etaleToProEt_derivedInverseImageIso f).symm
      (etaleToProEt_derivedPushforwardHomNat f) :=
  sorry

/-- Canonical derived comparison `ε⁻¹ (Rf_étale,* F) ⟶ Rf_proétale,* (ε⁻¹ F)` at an abelian
sheaf `F` on `X_étale`. -/
def etaleToProEt_derivedPushforwardHom
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (ExactFunctor.Derived.Plus.functor (etaleToProEtPullbackExact Y)).obj
        ((Adjunction.Derived.Plus.right
            (smallEtaleSheafPushforward AddCommGrpCat.{u + 1} f)).obj
          ((DerivedCategory.Plus.singleFunctor
              (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (0 : ℤ)).obj F)) ⟶
      (Adjunction.Derived.Plus.right
          (proEtSheafPushforward AddCommGrpCat.{u + 1} f)).obj
        ((ExactFunctor.Derived.Plus.functor (etaleToProEtPullbackExact X)).obj
          ((DerivedCategory.Plus.singleFunctor
              (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (0 : ℤ)).obj F)) :=
  (etaleToProEt_derivedPushforwardHomNat f).app
    ((DerivedCategory.Plus.singleFunctor
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (0 : ℤ)).obj F)

/-- The derived comparison at an abelian sheaf is the component of the `D⁺` mate. -/
theorem etaleToProEt_derivedPushforwardHom_spec
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    etaleToProEt_derivedPushforwardHom f F =
      (etaleToProEt_derivedPushforwardHomNat f).app
        ((DerivedCategory.Plus.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (0 : ℤ)).obj F) :=
  sorry

end Abelian

section PushforwardComparison

variable (f : X ⟶ Y)

/-- For a quasi-compact quasi-separated morphism `f : X ⟶ Y` and a
sheaf of sets `F` on `X_étale`, the canonical mate
`ε⁻¹ (f_étale,* F) ⟶ f_proétale,* (ε⁻¹ F)` is an isomorphism. -/
instance etaleToProEt_pushforwardHom_isIso
    [QuasiCompact f] [QuasiSeparated f]
    [∀ F : Y.Etaleᵒᵖ ⥤ Type (u + 1), (etaleToProEt Y).op.HasLeftKanExtension F]
    [∀ F : X.Etaleᵒᵖ ⥤ Type (u + 1), (etaleToProEt X).op.HasLeftKanExtension F]
    [∀ F : Y.Etaleᵒᵖ ⥤ Type (u + 1), (smallEtalePullback f).op.HasLeftKanExtension F]
    [∀ F : Y.ProEtᵒᵖ ⥤ Type (u + 1), (baseChange f).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
    [HasWeakSheafify (topology X) (Type (u + 1))]
    [HasWeakSheafify (topology Y) (Type (u + 1))]
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    IsIso ((etaleToProEt_pushforwardHom (Type (u + 1)) f).app F) :=
  sorry

/-- For a quasi-compact quasi-separated morphism `f : X ⟶ Y` and an
abelian sheaf `F` on `X_étale`, the canonical mate
`ε⁻¹ (Rf_étale,* F) ⟶ Rf_proétale,* (ε⁻¹ F)` is an isomorphism. -/
instance etaleToProEt_derivedPushforwardHom_isIso
    [QuasiCompact f] [QuasiSeparated f]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify (topology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (topology Y) AddCommGrpCat.{u + 1}]
    [∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (etaleToProEt Y).op.HasLeftKanExtension F]
    [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (etaleToProEt X).op.HasLeftKanExtension F]
    [∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallEtalePullback f).op.HasLeftKanExtension F]
    [∀ F : Y.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (baseChange f).op.HasLeftKanExtension F]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso (etaleToProEt_derivedPushforwardHom f F) :=
  sorry

end PushforwardComparison

end AlgebraicGeometry.Scheme

