module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose
public import stacks_project.Chap63.Lemma_63_4_3
public import stacks_project.Chap63.Lemma_63_7_3_ExtensionByZero
public import stacks_project.Chap63.Lemma_63_8_1_Comparison
public import stacks_project.Chap63.Lemma_63_11_2_Comparison

/-!
# Uniqueness comparison of derived étale upper shriek with inverse image

Along a separated étale morphism, uniqueness of adjoints identifies
`Rf^!` with étale inverse image `j⁻¹`, using the sheaf-level identification
`j_! ≅ f_!` of Lemma 63.4.3.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

section ExtensionByZero

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] [LocallyQuasiFinite j]
variable (Λ : Type u) [CommRing Λ]
variable [U.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [X.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction j).op]
variable [LocallyOfFiniteType j]
variable [HasWeakSheafify U.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ V : U.Etale,
  HasWeakSheafify (U.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
variable [∀ V : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [(etaleExtensionByZero j (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero j (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits (etaleExtensionByZero j (ModuleCat.{u} Λ))]
variable [(etaleRestrictionSheaf j (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleRestrictionSheaf j (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits (etaleRestrictionSheaf j (ModuleCat.{u} Λ))]
variable [IsGrothendieckAbelian (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- Forgetting coefficients identifies étale extension by zero of a sheaf of
`Λ`-modules with abelian extension by zero of the underlying abelian sheaf. -/
def etaleExtensionByZero_forget
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((etaleExtensionByZero j (ModuleCat.{u} Λ)).obj F) ≅
      (abelianExtensionByZero j).obj
        ((sheafCompose U.smallEtaleTopology
            (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F) :=
  (Functor.sheafPullback.compSheafComposeIso
      (etaleRestriction j) (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})
      U.smallEtaleTopology X.smallEtaleTopology).app F

/-- Forgetting coefficients identifies module-valued compact-support direct
image with abelian finite-support lower shriek. -/
def lowerShriekModuleIsoExtensionByZero_forget
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((lowerShriekModule j Λ).obj F) ≅
      (lowerShriek j).obj
        ((sheafCompose U.smallEtaleTopology
            (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F) :=
  (lowerShriekModule_forgetFunctorIso j Λ).app F

/-- The component of the sheaf-level identification `j_! ≅ f_!` at a sheaf of
`Λ`-modules. -/
def lowerShriekModuleIsoExtensionByZero_app
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (etaleExtensionByZero j (ModuleCat.{u} Λ)).obj F ≅
      (lowerShriekModule j Λ).obj F where
  hom :=
    liftModuleSheafHom
      ((etaleExtensionByZero_forget j Λ F).hom ≫
        ((extensionByZeroIsoLowerShriek j).app
            ((sheafCompose U.smallEtaleTopology
                (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)).hom ≫
        (lowerShriekModuleIsoExtensionByZero_forget j Λ F).inv)
  inv :=
    liftModuleSheafHom
      ((lowerShriekModuleIsoExtensionByZero_forget j Λ F).hom ≫
        ((extensionByZeroIsoLowerShriek j).symm.app
            ((sheafCompose U.smallEtaleTopology
                (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)).hom ≫
        (etaleExtensionByZero_forget j Λ F).inv)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Sheaf-level identification of étale extension by zero with finite-support
lower shriek on étale sheaves of `Λ`-modules. -/
def lowerShriekModuleIsoExtensionByZero :
    etaleExtensionByZero j (ModuleCat.{u} Λ) ≅ lowerShriekModule j Λ :=
  NatIso.ofComponents (lowerShriekModuleIsoExtensionByZero_app j Λ) sorry

/-- Derived identification `f_! ≅ j_!` induced by the sheaf-level comparison. -/
def lowerShriekModuleDerivedIsoExtensionByZero :
    lowerShriekModuleDerived j Λ ≅ etaleDerivedExtensionByZero j Λ :=
  Functor.MapDerivedCategory.functorIso
    (lowerShriekModuleIsoExtensionByZero j Λ).symm

/-- Compactification-free uniqueness isomorphism identifying the K-injective
derived upper shriek of Section 63.7 with étale inverse image. -/
def upperShriekModuleDerivedIsoRestriction :
    upperShriekModuleDerived j Λ ≅ etaleDerivedRestriction j Λ :=
  conjugateIsoEquiv (lowerShriekModuleDerivedAdjunction j Λ)
    (etaleDerivedExtensionByZeroAdjunction j Λ)
    (lowerShriekModuleDerivedIsoExtensionByZero j Λ).symm

/-- Objectwise evaluation of `upperShriekModuleDerivedIsoRestriction`. -/
def upperShriekModuleDerivedIsoRestriction_app (K : EtaleDerived X Λ) :
    (upperShriekModuleDerived j Λ).obj K ≅
      (etaleDerivedRestriction j Λ).obj K :=
  (upperShriekModuleDerivedIsoRestriction j Λ).app K

end ExtensionByZero

variable {Y : Scheme.{u}} (X : Over Y) (Λ : Type u) [CommRing Λ]
variable [IsSeparated X.hom] [Scheme.Hom.QuasiFinite X.hom] [Etale X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (P : Compactification.Of Y X)
variable [IsFinite P.obj.right.hom]
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      P.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [PreservesFiniteLimits
  ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology)]
variable [PreservesFiniteColimits
  ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology)]
variable [X.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [P.obj.right.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [P.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Compactification.Of.ι P)).op]
variable [IsGrothendieckAbelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [((etaleDerivedLowerShriek X P :
    EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ)).IsLeftAdjoint]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction X.hom).op.HasLeftKanExtension F]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction X.hom).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero X.hom (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero X.hom (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits (etaleExtensionByZero X.hom (ModuleCat.{u} Λ))]
variable [(etaleRestrictionSheaf X.hom (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleRestrictionSheaf X.hom (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits (etaleRestrictionSheaf X.hom (ModuleCat.{u} Λ))]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction X.hom).op]

/-- The compactification presentation `Rf_!` agrees with étale extension by
zero `j_!` on unbounded derived categories. -/
def etaleDerivedLowerShriekIsoExtensionByZero :
    (etaleDerivedLowerShriek X P :
        EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ) ≅
      etaleDerivedExtensionByZero X.hom Λ :=
  etaleDerivedLowerShriekIsoModuleDerived X Λ P ≪≫
    lowerShriekModuleDerivedIsoExtensionByZero X.hom Λ

/-- The uniqueness isomorphism identifying compactification `Rf^!` with étale
inverse image, as the mate of `etaleDerivedLowerShriekIsoExtensionByZero`. -/
def etaleDerivedUpperShriekComparisonIsoRestriction :
    etaleDerivedUpperShriek X Λ P ≅ etaleDerivedRestriction X.hom Λ :=
  conjugateIsoEquiv (etaleDerivedLowerShriekAdjunction X Λ P)
    (etaleDerivedExtensionByZeroAdjunction X.hom Λ)
    (etaleDerivedLowerShriekIsoExtensionByZero X Λ P).symm

/-- Objectwise evaluation of `etaleDerivedUpperShriekComparisonIsoRestriction`. -/
def etaleDerivedUpperShriekComparisonIsoRestriction_app
    (K : EtaleDerived Y Λ) :
    (etaleDerivedUpperShriek X Λ P).obj K ≅
      (etaleDerivedRestriction X.hom Λ).obj K :=
  (etaleDerivedUpperShriekComparisonIsoRestriction X Λ P).app K

/-- The comparison isomorphism is the conjugate of the inverse of
`etaleDerivedLowerShriekIsoExtensionByZero` along the two derived
adjunctions. -/
theorem etaleDerivedUpperShriekComparisonIsoRestriction_spec :
    etaleDerivedUpperShriekComparisonIsoRestriction X Λ P =
      conjugateIsoEquiv (etaleDerivedLowerShriekAdjunction X Λ P)
        (etaleDerivedExtensionByZeroAdjunction X.hom Λ)
        (etaleDerivedLowerShriekIsoExtensionByZero X Λ P).symm :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
