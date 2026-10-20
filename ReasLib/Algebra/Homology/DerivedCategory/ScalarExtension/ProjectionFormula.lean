/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Tensor.HomologicalComplex.ProjectionFormula
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction
public import ReasLib.Algebra.Homology.DerivedCategory.TensorProduct
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived restriction/extension projection formula

For a ring homomorphism `σ : R →+* S`, restriction after extension of scalars is tensoring by
the restricted regular `S`-module.  This leaf owns the generic object-level comparison used by
localization and completion chapters.  The concrete tensor maps are assembled from the
cochain-level change-of-rings owner; only naturality and derived universal-property statements
remain deferred.

@stack 064M
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe u

namespace CategoryTheory.ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The regular `S`-module, restricted to an `R`-module along `σ`. -/
@[stacks 064M "restricted regular module"]
noncomputable abbrev restrictedRegular (σ : R →+* S) : ModuleCat R :=
  (ModuleCat.restrictScalars σ).obj (ModuleCat.of S S)

/-- The degree-zero derived object of the restricted regular module. -/
@[stacks 064M "restricted regular derived object"]
noncomputable abbrev restrictedRegular₀ (σ : R →+* S) :
    DerivedCategory (ModuleCat R) :=
  ModuleCat.single0 (restrictedRegular σ)

/-- The chosen degree-zero cochain representative of the restricted regular module. -/
@[stacks 064M "restricted regular cochain representative"]
noncomputable abbrev restrictedRegularComplex (σ : R →+* S) :
    CochainComplex (ModuleCat R) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj
    (restrictedRegular σ)

/-- The cochain complex obtained by extending and then restricting scalars. -/
@[stacks 064M "extension restriction cochain source"]
noncomputable abbrev extensionRestrictionComplex (σ : R →+* S) :
    CochainComplex (ModuleCat R) ℤ ⥤ CochainComplex (ModuleCat R) ℤ :=
  (ModuleCat.extendScalars σ).mapHomologicalComplex (up ℤ) ⋙
    (ModuleCat.restrictScalars σ).mapHomologicalComplex (up ℤ)

/-- The cochain tensor functor with the restricted regular module on the left. -/
@[stacks 064M "projection-formula cochain tensor source"]
noncomputable abbrev projectionComplex (σ : R →+* S) :
    CochainComplex (ModuleCat R) ℤ ⥤ CochainComplex (ModuleCat R) ℤ :=
  ((curriedTensor (ModuleCat R)).map₂CochainComplex).obj
    (restrictedRegularComplex σ)

/- Tensoring a complex is functorial in the left factor; this explicit iso keeps the two
cochain-level maps concrete while its coherence fields remain proof obligations. -/
/-- The two coherence equations for `tensorLeftMapIso` are proposition-valued laws. -/
@[stacks 064M "tensor map hom-inverse law"]
theorem tensorLeftMapIso_hom_inv_id
    {C : Type u} [CommRing C]
    {K L M : CochainComplex (ModuleCat C) ℤ} (e : K ≅ L) :
    HomologicalComplex.tensorHom e.hom (𝟙 M) ≫
        HomologicalComplex.tensorHom e.inv (𝟙 M) = 𝟙 _ := sorry

/-- The inverse-then-forward coherence equation for `tensorLeftMapIso`. -/
@[stacks 064M "tensor map inverse-hom law"]
theorem tensorLeftMapIso_inv_hom_id
    {C : Type u} [CommRing C]
    {K L M : CochainComplex (ModuleCat C) ℤ} (e : K ≅ L) :
    HomologicalComplex.tensorHom e.inv (𝟙 M) ≫
        HomologicalComplex.tensorHom e.hom (𝟙 M) = 𝟙 _ := sorry

/- The preceding law declarations supply the proof fields of this concrete isomorphism. -/
/- The public declaration remains a data owner; no carrier or map is chosen by `sorry`. -/
/-- The concrete tensor map isomorphism with the two law fields supplied above. -/
@[stacks 064M "cochain tensor map isomorphism"]
noncomputable def tensorLeftMapIso
    {C : Type u} [CommRing C]
    {K L M : CochainComplex (ModuleCat C) ℤ} (e : K ≅ L) :
    HomologicalComplex.tensorObj K M ≅ HomologicalComplex.tensorObj L M where
  hom := HomologicalComplex.tensorHom e.hom (𝟙 M)
  inv := HomologicalComplex.tensorHom e.inv (𝟙 M)
  hom_inv_id := tensorLeftMapIso_hom_inv_id e
  inv_hom_id := tensorLeftMapIso_inv_hom_id e

/-- The explicit cochain-level projection comparison, naturality deferred to a named theorem. -/
@[stacks 064M "projection-formula cochain comparison"]
noncomputable def projectionComplexComponentIso (σ : R →+* S)
    (K : CochainComplex (ModuleCat R) ℤ) :
    (extensionRestrictionComplex σ).obj K ≅ (projectionComplex σ).obj K :=
  let singleS : CochainComplex (ModuleCat S) ℤ :=
    (CochainComplex.singleFunctor (ModuleCat S) (0 : ℤ)).obj (ModuleCat.of S S)
  let extK := ((ModuleCat.extendScalars σ).mapHomologicalComplex (up ℤ)).obj K
  let res := (ModuleCat.restrictScalars σ).mapHomologicalComplex (up ℤ)
  let eSingle :=
    (Functor.mapCochainComplexSingleFunctor
      (ModuleCat.restrictScalars σ) (0 : ℤ)).app (ModuleCat.of S S)
  (res.mapIso ((λ_ extK).symm)) ≪≫
    (ModuleCat.RestrictScalars.tensorObjExtendIso σ singleS K) ≪≫
    (tensorLeftMapIso eSingle)

/-- The natural cochain-level projection comparison assembled from the component isomorphisms. -/
@[stacks 064M "naturality of the cochain projection comparison"]
theorem projectionComplexIso_naturality (σ : R →+* S) :
    ∀ (K L : CochainComplex (ModuleCat R) ℤ) (f : K ⟶ L),
      (extensionRestrictionComplex σ).map f ≫
          (projectionComplexComponentIso σ L).hom =
        (projectionComplexComponentIso σ K).hom ≫ (projectionComplex σ).map f := sorry

/-- The natural isomorphism assembled from the explicit component maps. -/
@[stacks 064M "projection-formula cochain comparison"]
noncomputable def projectionComplexIso (σ : R →+* S) :
    extensionRestrictionComplex σ ≅ projectionComplex σ :=
  NatIso.ofComponents (projectionComplexComponentIso σ)
    (fun {K L} f => projectionComplexIso_naturality σ K L f)

/-- Compatibility spelling for the canonical quotient/totalization comparison used to pass from a
tensor complex to its derived object. -/
@[stacks 064M "derived tensor complex comparison"]
noncomputable abbrev quotientTensorIso
    (K L : CochainComplex (ModuleCat R) ℤ) :
    (DerivedCategory.Qh :
      HomotopyCategory (ModuleCat R) (up ℤ) ⥤ DerivedCategory (ModuleCat R)).obj
        ((HomotopyCategory.quotient (ModuleCat R) (up ℤ)).obj K ⊗
          (HomotopyCategory.quotient (ModuleCat R) (up ℤ)).obj L) ≅
      (DerivedCategory.Q : CochainComplex (ModuleCat R) ℤ ⥤
        DerivedCategory (ModuleCat R)).obj (HomologicalComplex.tensorObj K L) :=
  DerivedCategory.DerivedTensor.Bifunctor.sourceFunctorObjIso K L

/-- A morphism in the varying (right) derived-tensor parameter, transported through the canonical
two-variable model. -/
@[stacks 064M "derived tensor parameter map"]
noncomputable def derivedTensorParameterMap (E : DerivedCategory (ModuleCat R))
    {X Y : DerivedCategory (ModuleCat R)} (f : X ⟶ Y) :
    (DerivedCategory.derivedTensorProduct X).obj E ⟶
      (DerivedCategory.derivedTensorProduct Y).obj E :=
  (DerivedCategory.DerivedTensorProduct.objIsoBifunctor E X).hom ≫
    (DerivedCategory.DerivedTensor.Bifunctor.functor (C := ModuleCat R)).map
      (Prod.mkHom (𝟙 E) f) ≫
    (DerivedCategory.DerivedTensorProduct.objIsoBifunctor E Y).inv

/-- The cochain-level counit for extension followed by restriction, with the target written using
the explicit restricted cochain functor. -/
@[stacks 064M "extension-restriction cochain counit"]
noncomputable def extensionRestrictionCochainCounit (σ : R →+* S) :
    (DerivedCategory.Q : CochainComplex (ModuleCat R) ℤ ⥤
      DerivedCategory (ModuleCat R)) ⋙
        (derivedExtensionOfScalars σ ⋙ derivedRestrictionOfScalars σ) ⟶
      extensionRestrictionComplex σ ⋙
        (DerivedCategory.Q : CochainComplex (ModuleCat R) ℤ ⥤
          DerivedCategory (ModuleCat R)) :=
  (Functor.associator
      (DerivedCategory.Q : CochainComplex (ModuleCat R) ℤ ⥤
        DerivedCategory (ModuleCat R))
      (derivedExtensionOfScalars σ) (derivedRestrictionOfScalars σ)).inv ≫
    Functor.whiskerRight (derivedExtensionComplexCounit σ)
      (derivedRestrictionOfScalars σ) ≫
    Functor.whiskerLeft
      ((ModuleCat.extendScalars σ).mapHomologicalComplex (up ℤ))
      (ModuleCat.restrictScalars σ).mapDerivedCategoryFactors.hom

/- The cochain-level counit for the fixed-left view of the two-variable derived tensor. -/
/-- The component is concrete; only its naturality equation is deferred below. -/
@[stacks 064M "fixed-left tensor counit component"]
noncomputable def projectionCochainCounitApp (σ : R →+* S)
    (K : CochainComplex (ModuleCat R) ℤ) :=
  let L := restrictedRegularComplex σ
  let e :=
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app
      (restrictedRegular σ)
  (DerivedCategory.DerivedTensor.Bifunctor.functor (C := ModuleCat R)).map
      (Prod.mkHom e.hom (𝟙 _)) ≫
    DerivedCategory.DerivedTensor.Bifunctor.counitAppOfQ L K

/-- The fixed-left tensor counit component is natural in the cochain complex. -/
@[stacks 064M "naturality of the fixed-left tensor counit"]
theorem projectionCochainCounit_naturality (σ : R →+* S) :
    ∀ ⦃K K' : CochainComplex (ModuleCat R) ℤ⦄ (f : K ⟶ K'),
      ((DerivedCategory.Q : CochainComplex (ModuleCat R) ℤ ⥤
          DerivedCategory (ModuleCat R)) ⋙
        DerivedCategory.DerivedTensor.Bifunctor.leftFunctor (restrictedRegular₀ σ)).map f ≫
          projectionCochainCounitApp σ K' =
        projectionCochainCounitApp σ K ≫
          ((projectionComplex σ ⋙
            (DerivedCategory.Q : CochainComplex (ModuleCat R) ℤ ⥤
              DerivedCategory (ModuleCat R))).map f) := sorry

/- The component and its naturality theorem assemble the concrete counit below. -/
/-- The concrete fixed-left counit natural transformation. -/
@[stacks 064M "fixed-left tensor cochain counit"]
noncomputable def projectionCochainCounit (σ : R →+* S) :
    (DerivedCategory.Q : CochainComplex (ModuleCat R) ℤ ⥤
      DerivedCategory (ModuleCat R)) ⋙
        DerivedCategory.DerivedTensor.Bifunctor.leftFunctor (restrictedRegular₀ σ) ⟶
      projectionComplex σ ⋙
        (DerivedCategory.Q : CochainComplex (ModuleCat R) ℤ ⥤
          DerivedCategory (ModuleCat R)) :=
  { app := projectionCochainCounitApp σ
    naturality := projectionCochainCounit_naturality σ }

/-- The fixed-left two-variable tensor model satisfies the cochain-level left-derived law.  This
is a Prop gate: its proof can later be replaced by a K-flat/resolution construction without
changing any comparison data below. -/
@[stacks 064M "fixed-left tensor left-derived gate"]
instance projectionCochainIsLeftDerived (σ : R →+* S) :
    (DerivedCategory.DerivedTensor.Bifunctor.leftFunctor (restrictedRegular₀ σ)).IsLeftDerivedFunctor
      (projectionCochainCounit σ)
      (HomologicalComplex.quasiIso (ModuleCat R) (up ℤ)) := sorry

/-- The extension/restriction cochain counit has the canonical left-derived law. -/
@[stacks 064M "extension-restriction left-derived gate"]
instance extensionRestrictionCochainIsLeftDerived (σ : R →+* S) :
    (derivedExtensionOfScalars σ ⋙ derivedRestrictionOfScalars σ).IsLeftDerivedFunctor
      (extensionRestrictionCochainCounit σ)
      (HomologicalComplex.quasiIso (ModuleCat R) (up ℤ)) := sorry

/-- The source comparison after passing to the derived category. -/
@[stacks 064M "derived projection source comparison"]
noncomputable def projectionDerivedNatIsoOf
    (σ : R →+* S)
    (h₁ : (derivedExtensionOfScalars σ ⋙ derivedRestrictionOfScalars σ).IsLeftDerivedFunctor
      (extensionRestrictionCochainCounit σ)
      (HomologicalComplex.quasiIso (ModuleCat R) (up ℤ)))
    (h₂ : (DerivedCategory.DerivedTensor.Bifunctor.leftFunctor
      (restrictedRegular₀ σ)).IsLeftDerivedFunctor (projectionCochainCounit σ)
      (HomologicalComplex.quasiIso (ModuleCat R) (up ℤ))) :
    derivedExtensionOfScalars σ ⋙ derivedRestrictionOfScalars σ ≅
      DerivedCategory.DerivedTensor.Bifunctor.leftFunctor (restrictedRegular₀ σ) :=
  letI := h₁
  letI := h₂
  Functor.leftDerivedNatIso
    (derivedExtensionOfScalars σ ⋙ derivedRestrictionOfScalars σ)
    (DerivedCategory.DerivedTensor.Bifunctor.leftFunctor (restrictedRegular₀ σ))
    (extensionRestrictionCochainCounit σ) (projectionCochainCounit σ)
    (HomologicalComplex.quasiIso (ModuleCat R) (up ℤ))
    (Functor.isoWhiskerRight (projectionComplexIso σ)
      (DerivedCategory.Q : CochainComplex (ModuleCat R) ℤ ⥤
        DerivedCategory (ModuleCat R)))

/-- Canonical derived projection source comparison, using the registered Prop gates. -/
@[stacks 064M "canonical derived projection source comparison"]
noncomputable abbrev projectionDerivedNatIso (σ : R →+* S) :
    derivedExtensionOfScalars σ ⋙ derivedRestrictionOfScalars σ ≅
      DerivedCategory.DerivedTensor.Bifunctor.leftFunctor (restrictedRegular₀ σ) :=
  projectionDerivedNatIsoOf σ inferInstance inferInstance

/-- The derived object-level projection comparison for an explicit ring homomorphism and supplied
left-derived laws.  The laws are explicit parameters so this data owner does not select a proof
from a `Prop` instance. -/
@[stacks 064M "derived restriction/extension projection formula"]
noncomputable def restrictDerivedTensorIsoOf (σ : R →+* S)
    (h₁ : (derivedExtensionOfScalars σ ⋙ derivedRestrictionOfScalars σ).IsLeftDerivedFunctor
      (extensionRestrictionCochainCounit σ)
      (HomologicalComplex.quasiIso (ModuleCat R) (up ℤ)))
    (h₂ : (DerivedCategory.DerivedTensor.Bifunctor.leftFunctor
      (restrictedRegular₀ σ)).IsLeftDerivedFunctor (projectionCochainCounit σ)
      (HomologicalComplex.quasiIso (ModuleCat R) (up ℤ)))
    (X : DerivedCategory (ModuleCat R)) :
      (derivedRestrictionOfScalars σ).obj
        ((derivedExtensionOfScalars σ).obj X) ≅
      (DerivedCategory.derivedTensorProduct X).obj (restrictedRegular₀ σ) :=
  (projectionDerivedNatIsoOf σ h₁ h₂).app X ≪≫
    (DerivedCategory.DerivedTensorProduct.objIsoBifunctor
      (restrictedRegular₀ σ) X).symm

/-- Canonical facade for `restrictDerivedTensorIsoOf`, using the registered Prop gates. -/
@[stacks 064M "canonical derived restriction/extension projection formula"]
noncomputable abbrev restrictDerivedTensorIso (σ : R →+* S)
    (X : DerivedCategory (ModuleCat R)) :
    (derivedRestrictionOfScalars σ).obj
        ((derivedExtensionOfScalars σ).obj X) ≅
      (DerivedCategory.derivedTensorProduct X).obj (restrictedRegular₀ σ) :=
  restrictDerivedTensorIsoOf σ inferInstance inferInstance X

/-- Naturality of the derived restriction/extension projection comparison. -/
@[stacks 064M "naturality of derived projection formula"]
theorem restrictDerivedTensorIsoOf_naturality (σ : R →+* S)
    (h₁ : (derivedExtensionOfScalars σ ⋙ derivedRestrictionOfScalars σ).IsLeftDerivedFunctor
      (extensionRestrictionCochainCounit σ)
      (HomologicalComplex.quasiIso (ModuleCat R) (up ℤ)))
    (h₂ : (DerivedCategory.DerivedTensor.Bifunctor.leftFunctor
      (restrictedRegular₀ σ)).IsLeftDerivedFunctor (projectionCochainCounit σ)
      (HomologicalComplex.quasiIso (ModuleCat R) (up ℤ)))
    {X Y : DerivedCategory (ModuleCat R)} (f : X ⟶ Y) :
    (derivedRestrictionOfScalars σ).map
        ((derivedExtensionOfScalars σ).map f) ≫
        (restrictDerivedTensorIsoOf σ h₁ h₂ Y).hom =
      (restrictDerivedTensorIsoOf σ h₁ h₂ X).hom ≫
        (derivedTensorParameterMap (R := R) (restrictedRegular₀ σ) f) := sorry

/-- Naturality of the canonical derived restriction/extension projection comparison. -/
@[stacks 064M "naturality of canonical derived projection formula"]
theorem restrictDerivedTensorIso_naturality (σ : R →+* S)
    {X Y : DerivedCategory (ModuleCat R)} (f : X ⟶ Y) :
    (derivedRestrictionOfScalars σ).map
        ((derivedExtensionOfScalars σ).map f) ≫
        (restrictDerivedTensorIso σ Y).hom =
      (restrictDerivedTensorIso σ X).hom ≫
        (derivedTensorParameterMap (R := R) (restrictedRegular₀ σ) f) := sorry

/-- Compatibility spelling for `projectionDerivedNatIso`; the projection comparison has one
canonical natural-isomorphism owner. -/
@[stacks 064M "derived projection-formula natural isomorphism"]
noncomputable abbrev restrictDerivedTensorNatIso (σ : R →+* S) :
    derivedExtensionOfScalars σ ⋙ derivedRestrictionOfScalars σ ≅
      DerivedCategory.DerivedTensor.Bifunctor.leftFunctor (restrictedRegular₀ σ) :=
  projectionDerivedNatIso σ

end CategoryTheory.ModuleCat
