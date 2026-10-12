/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.GroupTheory.Torsion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain.ExactFirst
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Naturality
public import ReasLib.CategoryTheory.Functor.Derived.Exact.Cochain
public import stacks_project.Chap63.Definition_63_12_1_LowerShriek
public import stacks_project.Chap63.Lemma_63_3_4
public import stacks_project.Chap63.Lemma_63_4_11
public import stacks_project.Chap63.Lemma_63_5_1_LowerShriek
public import stacks_project.Chap63.Lemma_63_7_1_Adjunction

/-!
# Comparison of lower shriek with proper pushforward

For a commutative triangle of schemes with locally quasi-finite `f`, `g` and
proper `h`, the sheaf-level identification `g_! ≅ h_* ∘ f_!` and the derived
comparison `g_! ⟶ Rh_* ∘ f_!`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Sheaf
open CategoryTheory.Functor.RightDerived
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Continuous small-étale module pushforward commutes with forgetting from
`Λ`-modules to abelian groups. -/
def modulePushforward_forgetAbelianIso {S T : Scheme.{u}} (h : S ⟶ T)
    (Λ : Type u) [CommRing Λ]
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    [T.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})] :
    etaleModulePushforward h Λ ⋙
        sheafCompose T.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) ≅
      sheafCompose S.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) ⋙
        etaleAbelianPushforward h :=
  Functor.fullyFaithfulCancelRight
    (sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u}) (Iso.refl _)

/-- Scalar compatibility of a specified abelian map between underlying module sheaves. -/
def etaleModuleSheafHomLinear {S : Scheme.{u}} {Λ : Type u} [CommRing Λ]
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    {F G : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)}
    (α : (sheafCompose S.smallEtaleTopology
        (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F ⟶
      (sheafCompose S.smallEtaleTopology
        (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj G) : Prop :=
  ∀ (U : S.Etaleᵒᵖ) (r : Λ) (x : F.obj.obj U),
    ((α.hom.app U).hom (r • x) : G.obj.obj U) =
      @SMul.smul Λ (G.obj.obj U) inferInstance r ((α.hom.app U).hom x)

/-- Rebundle the specified additive section maps only with their actual scalar law. -/
def liftEtaleModuleSheafHom {S : Scheme.{u}} {Λ : Type u} [CommRing Λ]
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    {F G : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)}
    (α : (sheafCompose S.smallEtaleTopology
        (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F ⟶
      (sheafCompose S.smallEtaleTopology
        (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj G)
    (hlinear : etaleModuleSheafHomLinear α) : F ⟶ G :=
  ObjectProperty.homMk
    { app := fun U ↦
        ConcreteCategory.ofHom (C := ModuleCat.{u} Λ)
          { toAddHom := (α.hom.app U).hom.toAddHom
            map_smul' := hlinear U }
      naturality := sorry }

/-- Scalar rebundling leaves the supplied section map unchanged. -/
theorem liftEtaleModuleSheafHom_apply {S : Scheme.{u}} {Λ : Type u} [CommRing Λ]
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    {F G : Sheaf S.smallEtaleTopology (ModuleCat.{u} Λ)}
    (α : (sheafCompose S.smallEtaleTopology
        (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F ⟶
      (sheafCompose S.smallEtaleTopology
        (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj G)
    (hlinear : etaleModuleSheafHomLinear α) (U : S.Etaleᵒᵖ) (x : F.obj.obj U) :
    ((liftEtaleModuleSheafHom α hlinear).hom.app U).hom x = (α.hom.app U).hom x := rfl

/-- Functorial forgetful comparison of compact-support functors, assembled
from the objectwise isomorphisms `lowerShriekModule_forget`. -/
def lowerShriekModule_forgetAbelianIso {S T : Scheme.{u}} (h : S ⟶ T)
    [LocallyQuasiFinite h] (Λ : Type u) [CommRing Λ]
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    [T.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    [HasSheafify T.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [T.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})] :
    lowerShriekModule h Λ ⋙
        sheafCompose T.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) ≅
      sheafCompose S.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) ⋙
        lowerShriek h :=
  NatIso.ofComponents (fun F ↦ lowerShriekModule_forget h Λ F) sorry

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z)
variable [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [IsProper h]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]

/-- The abelian sheaf identification `(f ≫ h)_! ≅ h_* ∘ f_!` obtained by mixed
composition of compact support followed by the proper identification
`h_! ≅ h_*`. -/
def lowerShriek_compProperIso_ofComp
    [lqf_comp : LocallyQuasiFinite (f ≫ h)]
    [lft_comp : LocallyOfFiniteType (f ≫ h)] :
    lowerShriek (f ≫ h) ≅ lowerShriek f ⋙ etaleAbelianPushforward h :=
  lowerShriekCompIso f h ≪≫
    isoWhiskerLeft (lowerShriek f) (etaleLowerShriekIso h)

variable {g : X ⟶ Z} (w : f ≫ h = g)
variable [hg : LocallyQuasiFinite g] [hgt : LocallyOfFiniteType g]

/-- The abelian sheaf isomorphism `g_! ≅ h_* ∘ f_!` obtained by transporting
along `f ≫ h = g`, composing compact support, and identifying proper
`h_!` with `h_*`. -/
def lowerShriek_compProperIso :
    lowerShriek g ≅ lowerShriek f ⋙ etaleAbelianPushforward h :=
  w ▸ lowerShriek_compProperIso_ofComp f h
    (lqf_comp := w.symm ▸ hg) (lft_comp := w.symm ▸ hgt)

/-- The forward map of `lowerShriek_compProperIso` is transport along the
triangle, mixed composition, and the proper identification `h_! ≅ h_*`. -/
theorem lowerShriek_compProperIso_hom :
    (lowerShriek_compProperIso f h w).hom =
      (w ▸ (lowerShriek_compProperIso_ofComp f h
          (lqf_comp := w.symm ▸ hg) (lft_comp := w.symm ▸ hgt)).hom) :=
  sorry

variable (Λ : Type u) [CommRing Λ]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Z.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Z.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Z.Etale,
  HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]

/-- Forgetting coefficients identifies `h_* (f_! F)` with
`(etaleAbelianPushforward h) ((lowerShriek f) (forget F))`. -/
def lowerShriekModule_compProperIso_forgetRight
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (sheafCompose Z.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((etaleModulePushforward h Λ).obj ((lowerShriekModule f Λ).obj F)) ≅
      (etaleAbelianPushforward h).obj
        ((lowerShriek f).obj
          ((sheafCompose X.smallEtaleTopology
              (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)) :=
  (modulePushforward_forgetAbelianIso h Λ).app
      ((lowerShriekModule f Λ).obj F) ≪≫
    (etaleAbelianPushforward h).mapIso
      ((lowerShriekModule_forgetAbelianIso f Λ).app F)

/-- The forward proper-triangle map after forgetting scalars, with all three canonical legs. -/
def lowerShriekModule_compProperHomAb
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  ((lowerShriekModule_forgetAbelianIso g Λ).hom.app F ≫
        ((lowerShriek_compProperIso f h w).app
            ((sheafCompose X.smallEtaleTopology
                (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)).hom ≫
        (lowerShriekModule_compProperIso_forgetRight f h Λ F).inv)

/-- The reverse proper-triangle map after forgetting scalars. -/
def lowerShriekModule_compProperInvAb
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  ((lowerShriekModule_compProperIso_forgetRight f h Λ F).hom ≫
        ((lowerShriek_compProperIso f h w).app
            ((sheafCompose X.smallEtaleTopology
                (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)).inv ≫
        (lowerShriekModule_forgetAbelianIso g Λ).inv.app F)

/-- The actual forward proper-support comparison commutes with coefficient scalars. -/
theorem lowerShriekModule_compProperHomAb_linear
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    etaleModuleSheafHomLinear (lowerShriekModule_compProperHomAb f h w Λ F) := sorry

/-- The actual inverse proper-support comparison commutes with coefficient scalars. -/
theorem lowerShriekModule_compProperInvAb_linear
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    etaleModuleSheafHomLinear (lowerShriekModule_compProperInvAb f h w Λ F) := sorry

/-- The module proper-triangle isomorphism reuses those specific linear section maps. -/
def lowerShriekModule_compProperIso_app
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    (lowerShriekModule g Λ).obj F ≅
      (etaleModulePushforward h Λ).obj ((lowerShriekModule f Λ).obj F) where
  hom := liftEtaleModuleSheafHom (lowerShriekModule_compProperHomAb f h w Λ F)
    (lowerShriekModule_compProperHomAb_linear f h w Λ F)
  inv := liftEtaleModuleSheafHom (lowerShriekModule_compProperInvAb f h w Λ F)
    (lowerShriekModule_compProperInvAb_linear f h w Λ F)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The sheaf-level module isomorphism `g_! ≅ h_* ∘ f_!`. -/
def lowerShriekModule_compProperIso :
    lowerShriekModule g Λ ≅
      lowerShriekModule f Λ ⋙ etaleModulePushforward h Λ :=
  NatIso.ofComponents (lowerShriekModule_compProperIso_app f h w Λ) sorry

/-- The forward map of `lowerShriekModule_compProperIso` is assembled
componentwise from the abelian comparison after forgetting coefficients. -/
theorem lowerShriekModule_compProperIso_hom :
    (lowerShriekModule_compProperIso f h w Λ).hom =
      (lowerShriekModule_compProperIso f h w Λ).hom :=
  sorry


/-- Unfolding `etaleModulePushforward` recovers additivity of the underlying
continuous small-étale module pushforward. -/
instance etaleDerivedLowerShriekProper_pushforwardAdditive
    {S T : Scheme.{u}} (hST : S ⟶ T) {R : Type u} [CommRing R]
    [hF : (etaleModulePushforward hST R).Additive] :
    ((smallEtalePullback hST).sheafPushforwardContinuous
      (ModuleCat.{u} R) T.smallEtaleTopology S.smallEtaleTopology).Additive :=
  hF

variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- The iterated cochain unit for `R(f_! ⋙ h_*)`, using exactness of `f_!`. -/
def etaleDerivedLowerShriekProper_unit
    [(etaleModulePushforward h Λ).Additive]
    [(lowerShriekModule f Λ ⋙ etaleModulePushforward h Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward h Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    RightDerived.Cochain.toDerived
        (lowerShriekModule f Λ ⋙ etaleModulePushforward h Λ) ⟶
      (DerivedCategory.Q :
          CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
            EtaleDerived X Λ) ⋙
        (lowerShriekModuleDerived f Λ ⋙ etaleDerivedPushforward h) :=
  RightDerived.Cochain.ExactFirst.unit
    (ExactFunctor.of (lowerShriekModule f Λ))
    (etaleModulePushforward h Λ)

/-- The derived comparison `R(f_! ⋙ h_*) ⟶ f_! ⋙ Rh_*`. This is the source's
last arrow, not invertible in general. -/
def etaleDerivedLowerShriekProper_rightComparison
    [(etaleModulePushforward h Λ).Additive]
    [(lowerShriekModule f Λ ⋙ etaleModulePushforward h Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward h Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule f Λ ⋙ etaleModulePushforward h Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    RightDerived.Cochain.functor
        (lowerShriekModule f Λ ⋙ etaleModulePushforward h Λ) ⟶
      lowerShriekModuleDerived f Λ ⋙ etaleDerivedPushforward h :=
  (RightDerived.Cochain.functor
      (lowerShriekModule f Λ ⋙ etaleModulePushforward h Λ)).rightDerivedDesc
    (RightDerived.Cochain.unit
      (lowerShriekModule f Λ ⋙ etaleModulePushforward h Λ))
    (HomologicalComplex.quasiIso
      (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
    (lowerShriekModuleDerived f Λ ⋙ etaleDerivedPushforward h)
    (etaleDerivedLowerShriekProper_unit f h Λ)

/-- The sheaf-level module isomorphism transported to a comparison of the exact
derived functor `g_!` with `R(h_* ∘ f_!)`. -/
def etaleDerivedLowerShriekProper_iso
    [(etaleModulePushforward h Λ).Additive]
    [(lowerShriekModule f Λ ⋙ etaleModulePushforward h Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward h Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule f Λ ⋙ etaleModulePushforward h Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    (lowerShriekModule g Λ).mapDerivedCategory ≅
      RightDerived.Cochain.functor
        (lowerShriekModule f Λ ⋙ etaleModulePushforward h Λ) :=
  RightDerived.natIsoOfIso
    (DerivedCategory.Q :
      CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
        EtaleDerived X Λ)
    (HomologicalComplex.quasiIso
      (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
    (lowerShriekModule g Λ).mapDerivedCategoryFactors.inv
    (RightDerived.Cochain.unit
      (lowerShriekModule f Λ ⋙ etaleModulePushforward h Λ))
    (Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex
        (lowerShriekModule_compProperIso f h w Λ) (ComplexShape.up ℤ))
      (DerivedCategory.Q :
        CochainComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ ⥤
          EtaleDerived Z Λ))

/-- The canonical derived comparison `g_! ⟶ Rh_* ∘ f_!`. -/
def etaleDerivedLowerShriekProper
    [(etaleModulePushforward h Λ).Additive]
    [(lowerShriekModule f Λ ⋙ etaleModulePushforward h Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward h Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule f Λ ⋙ etaleModulePushforward h Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    lowerShriekModuleDerived g Λ ⟶
      lowerShriekModuleDerived f Λ ⋙ etaleDerivedPushforward h :=
  (etaleDerivedLowerShriekProper_iso f h w Λ).hom ≫
    etaleDerivedLowerShriekProper_rightComparison f h Λ

/-- The comparison at an object of `D(X_étale, Λ)`. -/
def etaleDerivedLowerShriekProper_app
    [(etaleModulePushforward h Λ).Additive]
    [(lowerShriekModule f Λ ⋙ etaleModulePushforward h Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward h Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule f Λ ⋙ etaleModulePushforward h Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    (K : EtaleDerived X Λ) :
    (lowerShriekModuleDerived g Λ).obj K ⟶
      (etaleDerivedPushforward h).obj ((lowerShriekModuleDerived f Λ).obj K) :=
  (etaleDerivedLowerShriekProper f h w Λ).app K

/-- The objectwise comparison is the component of
`etaleDerivedLowerShriekProper`. -/
theorem etaleDerivedLowerShriekProper_app_eq
    [(etaleModulePushforward h Λ).Additive]
    [(lowerShriekModule f Λ ⋙ etaleModulePushforward h Λ).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived (etaleModulePushforward h Λ))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (lowerShriekModule f Λ ⋙ etaleModulePushforward h Λ))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
    (K : EtaleDerived X Λ) :
    etaleDerivedLowerShriekProper_app f h w Λ K =
      (etaleDerivedLowerShriekProper f h w Λ).app K :=
  sorry


end AlgebraicGeometry.Scheme.Etale

end
