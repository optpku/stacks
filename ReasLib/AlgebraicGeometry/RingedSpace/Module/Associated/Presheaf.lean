/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Open
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor-presheaf model of an associated module sheaf

For `alpha : R →+* Γ(X, O_X)` and an `R`-module `M`, this file constructs the presheaf
`U ↦ O_X(U) ⊗_R M` explicitly, including its restriction maps. Its sheafification is canonically
isomorphic to `Associated.obj alpha M`.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Associated

variable {X : RingedSpace.{u}} {R : Type u} [CommRing R]

/-- The value `O_X(U) ⊗_R M` of the tensor presheaf on `U`. -/
@[stacks 01BH "tensor presheaf value"]
noncomputable abbrev tensorValue (alpha : R →+* X.globalSectionsRing)
    (M : ModuleCat.{u} R) (U : (Opens X)ᵒᵖ) :
    ModuleCat.{u} (X.ringCatSheaf.obj.obj U) :=
  (ModuleCat.extendScalars (X.globalSectionsToOpen alpha U.unop)).obj M

/-- The scalar-restriction comparison used to define a tensor-presheaf restriction map. -/
@[stacks 01BH "tensor-presheaf restriction isomorphism"]
noncomputable def tensorRestrictionIso (alpha : R →+* X.globalSectionsRing)
    (M : ModuleCat.{u} R) {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) :
    (ModuleCat.restrictScalars (X.globalSectionsToOpen alpha V.unop)).obj
        (tensorValue alpha M V) ≅
      (ModuleCat.restrictScalars (X.globalSectionsToOpen alpha U.unop)).obj
        ((ModuleCat.restrictScalars (X.ringCatSheaf.obj.map f).hom).obj
          (tensorValue alpha M V)) :=
  (ModuleCat.restrictScalarsCongr (X.globalSectionsToOpen_map alpha f)).app _ ≪≫
    (ModuleCat.restrictScalarsComp (X.globalSectionsToOpen alpha U.unop)
      (X.ringCatSheaf.obj.map f).hom).app _

/-- The restriction map `O_X(U) ⊗_R M → O_X(V) ⊗_R M`. -/
@[stacks 01BH "tensor-presheaf restriction map"]
noncomputable def tensorMap (alpha : R →+* X.globalSectionsRing)
    (M : ModuleCat.{u} R) {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) :
    tensorValue alpha M U ⟶
      (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map f).hom).obj
        (tensorValue alpha M V) :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (X.globalSectionsToOpen alpha U.unop)
    ((ModuleCat.extendRestrictScalarsAdj
      (X.globalSectionsToOpen alpha V.unop)).unit.app M ≫
        (tensorRestrictionIso alpha M f).hom)

/-- Tensor-presheaf restriction along an identity morphism is the canonical identity map. -/
theorem tensorMap_id (alpha : R →+* X.globalSectionsRing)
    (M : ModuleCat.{u} R) (U : (Opens X)ᵒᵖ) :
    tensorMap alpha M (𝟙 U) =
      (ModuleCat.restrictScalarsId' (X.ringCatSheaf.obj.map (𝟙 U)).hom
        (congrArg RingCat.Hom.hom (X.ringCatSheaf.obj.map_id U))).inv.app _ := sorry

/-- Tensor-presheaf restriction is compatible with composition. -/
theorem tensorMap_comp (alpha : R →+* X.globalSectionsRing)
    (M : ModuleCat.{u} R) {U V W : (Opens X)ᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) :
    tensorMap alpha M (f ≫ g) =
      tensorMap alpha M f ≫
        (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map f).hom).map
          (tensorMap alpha M g) ≫
        (ModuleCat.restrictScalarsComp' (X.ringCatSheaf.obj.map f).hom
          (X.ringCatSheaf.obj.map g).hom (X.ringCatSheaf.obj.map (f ≫ g)).hom
          (congrArg RingCat.Hom.hom (X.ringCatSheaf.obj.map_comp f g))).inv.app _ := sorry

/-- The explicit presheaf `U ↦ O_X(U) ⊗_R M`. -/
@[stacks 01BH "tensor presheaf"]
noncomputable def tensorPresheaf (alpha : R →+* X.globalSectionsRing)
    (M : ModuleCat.{u} R) : PresheafOfModules X.ringCatSheaf.obj where
  obj U := tensorValue alpha M U
  map f := tensorMap alpha M f
  map_id U := tensorMap_id alpha M U
  map_comp f g := tensorMap_comp alpha M f g

/-- Naturality of scalar extension on tensor-presheaf restriction maps. -/
theorem tensorPresheafMap_naturality (alpha : R →+* X.globalSectionsRing)
    {M N : ModuleCat.{u} R} (f : M ⟶ N) {U V : (Opens X)ᵒᵖ} (g : U ⟶ V) :
    tensorMap alpha M g ≫
        (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map g).hom).map
          ((ModuleCat.extendScalars (X.globalSectionsToOpen alpha V.unop)).map f) =
      (ModuleCat.extendScalars (X.globalSectionsToOpen alpha U.unop)).map f ≫
        tensorMap alpha N g := sorry

/-- The morphism of tensor presheaves induced by a morphism of `R`-modules. -/
@[stacks 01BH "tensor-presheaf morphism"]
noncomputable def tensorPresheafMap (alpha : R →+* X.globalSectionsRing)
    {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    tensorPresheaf alpha M ⟶ tensorPresheaf alpha N where
  app U := (ModuleCat.extendScalars (X.globalSectionsToOpen alpha U.unop)).map f
  naturality g := tensorPresheafMap_naturality alpha f g

/-- Tensor-presheaf maps preserve identity morphisms. -/
theorem tensorPresheafMap_id (alpha : R →+* X.globalSectionsRing)
    (M : ModuleCat.{u} R) :
    tensorPresheafMap alpha (𝟙 M) = 𝟙 (tensorPresheaf alpha M) := sorry

/-- Tensor-presheaf maps preserve composition. -/
theorem tensorPresheafMap_comp (alpha : R →+* X.globalSectionsRing)
    {M N P : ModuleCat.{u} R} (f : M ⟶ N) (g : N ⟶ P) :
    tensorPresheafMap alpha (f ≫ g) =
      tensorPresheafMap alpha f ≫ tensorPresheafMap alpha g := sorry

/-- Lemma 17.10.5 (01BH) (2), functorial tensor model: `M ↦ (U ↦ O_X(U) ⊗_R M)` is a
functor to presheaves of modules. -/
@[stacks 01BH "(2), tensor-presheaf functor"]
noncomputable def presheafFunctor (alpha : R →+* X.globalSectionsRing) :
    ModuleCat.{u} R ⥤ PresheafOfModules X.ringCatSheaf.obj where
  obj M := tensorPresheaf alpha M
  map f := tensorPresheafMap alpha f
  map_id M := tensorPresheafMap_id alpha M
  map_comp f g := tensorPresheafMap_comp alpha f g

/-- The canonical map from the tensor value on `U` to the associated module sheaf on `U`. -/
@[stacks 01BH "sectionwise tensor comparison"]
noncomputable def tensorComparisonApp (alpha : R →+* X.globalSectionsRing)
    (M : ModuleCat.{u} R) (U : (Opens X)ᵒᵖ) :
    tensorValue alpha M U ⟶ (obj alpha M).val.obj U :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (X.globalSectionsToOpen alpha U.unop)
    ((adjunction alpha).unit.app M ≫
      X.moduleGlobalSectionsToOpen alpha (obj alpha M) U.unop)

/-- The tensor comparison maps commute with restriction to smaller opens. -/
theorem tensorComparisonApp_naturality (alpha : R →+* X.globalSectionsRing)
    (M : ModuleCat.{u} R) {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) :
    tensorMap alpha M f ≫
        (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map f).hom).map
          (tensorComparisonApp alpha M V) =
      tensorComparisonApp alpha M U ≫ (obj alpha M).val.map f := sorry

/-- The canonical morphism from `U ↦ O_X(U) ⊗_R M` to the presheaf underlying the associated
module sheaf. -/
@[stacks 01BH "tensor comparison"]
noncomputable def tensorComparison (alpha : R →+* X.globalSectionsRing)
    (M : ModuleCat.{u} R) :
    tensorPresheaf alpha M ⟶
      (SheafOfModules.forget X.ringCatSheaf).obj (obj alpha M) where
  app U := tensorComparisonApp alpha M U
  naturality f := tensorComparisonApp_naturality alpha M f

/-- The tensor comparison with codomain restricted along the identity ring-presheaf map. -/
@[stacks 01BH "restricted tensor comparison"]
noncomputable def restrictedTensorComparison (alpha : R →+* X.globalSectionsRing)
    (M : ModuleCat.{u} R) :
    tensorPresheaf alpha M ⟶
      (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj
        ((SheafOfModules.forget X.ringCatSheaf).obj (obj alpha M)) :=
  tensorComparison alpha M ≫
    (PresheafOfModules.Restriction.idIso X.ringCatSheaf.obj).hom.app
      ((SheafOfModules.forget X.ringCatSheaf).obj (obj alpha M))

/-- Lemma 17.10.5 (01BH) (2), functorial form: sheafification of the tensor-presheaf functor. -/
@[stacks 01BH "(2), tensor-sheaf functor"]
noncomputable def sheafFunctor (alpha : R →+* X.globalSectionsRing) :
    ModuleCat.{u} R ⥤ X.Modules :=
  presheafFunctor alpha ⋙
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

/-- The sheafification of the explicit tensor presheaf. -/
@[stacks 01BH "tensor sheafification"]
noncomputable abbrev fromPresheaf (alpha : R →+* X.globalSectionsRing)
    (M : ModuleCat.{u} R) : X.Modules :=
  (sheafFunctor alpha).obj M

/-- The comparison from the sheafified tensor presheaf to the associated module sheaf. -/
@[stacks 01BH "sheafified tensor comparison"]
noncomputable def fromPresheafComparison (alpha : R →+* X.globalSectionsRing)
    (M : ModuleCat.{u} R) : fromPresheaf alpha M ⟶ obj alpha M :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).symm
    (restrictedTensorComparison alpha M)

/-- The canonical map from `M` to the global sections of its sheafified tensor model. -/
@[stacks 01BH "unit into the sheafified tensor model"]
noncomputable def fromPresheafUnit (alpha : R →+* X.globalSectionsRing)
    (M : ModuleCat.{u} R) :
    M ⟶ X.moduleGlobalSectionsRestriction alpha (fromPresheaf alpha M) :=
  (ModuleCat.extendRestrictScalarsAdj
      (X.globalSectionsToOpen alpha (⊤ : Opens X))).unit.app M ≫
    (ModuleCat.restrictScalars
      (X.globalSectionsToOpen alpha (⊤ : Opens X))).map
        ((SheafOfModules.RingedSite.moduleSheafificationUnitToVal
          X.sheaf (tensorPresheaf alpha M)).app (op (⊤ : Opens X))) ≫
    (ModuleCat.restrictScalarsCongr
      (X.globalSectionsToOpen_top alpha)).hom.app
        ((fromPresheaf alpha M).val.obj (op (⊤ : Opens X)))

/-- The explicit inverse of the sheafified tensor comparison, classified by the canonical map
into global sections. -/
@[stacks 01BH "inverse sheafified tensor comparison"]
noncomputable def fromPresheafComparisonInv (alpha : R →+* X.globalSectionsRing)
    (M : ModuleCat.{u} R) : obj alpha M ⟶ fromPresheaf alpha M :=
  (homEquiv alpha M (fromPresheaf alpha M)).symm (fromPresheafUnit alpha M)

/-- Under the associated-sheaf Hom equivalence, the explicit inverse is the canonical unit into
global sections of the sheafified tensor model. -/
@[simp, stacks 01BH "inverse tensor comparison under the Hom equivalence"]
theorem homEquiv_fromPresheafComparisonInv (alpha : R →+* X.globalSectionsRing)
    (M : ModuleCat.{u} R) :
    homEquiv alpha M (fromPresheaf alpha M) (fromPresheafComparisonInv alpha M) =
      fromPresheafUnit alpha M := sorry

/-- The sheafified tensor comparison followed by its explicit inverse is the identity. -/
@[simp, stacks 01BH "sheafified tensor comparison forward-inverse law"]
theorem fromPresheafComparison_hom_inv_id (alpha : R →+* X.globalSectionsRing)
    (M : ModuleCat.{u} R) :
    fromPresheafComparison alpha M ≫ fromPresheafComparisonInv alpha M = 𝟙 _ := sorry

/-- The explicit inverse followed by the sheafified tensor comparison is the identity. -/
@[simp, stacks 01BH "sheafified tensor comparison inverse-forward law"]
theorem fromPresheafComparison_inv_hom_id (alpha : R →+* X.globalSectionsRing)
    (M : ModuleCat.{u} R) :
    fromPresheafComparisonInv alpha M ≫ fromPresheafComparison alpha M = 𝟙 _ := sorry

/-- The sheafified tensor model is canonically isomorphic to the associated module sheaf, with
both directions explicitly owned. -/
@[stacks 01BH "sheafified tensor comparison isomorphism"]
noncomputable def fromPresheafComparisonIso (alpha : R →+* X.globalSectionsRing)
    (M : ModuleCat.{u} R) : fromPresheaf alpha M ≅ obj alpha M where
  hom := fromPresheafComparison alpha M
  inv := fromPresheafComparisonInv alpha M
  hom_inv_id := fromPresheafComparison_hom_inv_id alpha M
  inv_hom_id := fromPresheafComparison_inv_hom_id alpha M

/-- The forward map of `fromPresheafComparisonIso` is the named tensor comparison. -/
@[simp, stacks 01BH "sheafified tensor comparison isomorphism hom"]
theorem fromPresheafComparisonIso_hom (alpha : R →+* X.globalSectionsRing)
    (M : ModuleCat.{u} R) :
    (fromPresheafComparisonIso alpha M).hom = fromPresheafComparison alpha M := sorry

/-- The inverse map of `fromPresheafComparisonIso` is the named explicit inverse. -/
@[simp, stacks 01BH "sheafified tensor comparison isomorphism inverse"]
theorem fromPresheafComparisonIso_inv (alpha : R →+* X.globalSectionsRing)
    (M : ModuleCat.{u} R) :
    (fromPresheafComparisonIso alpha M).inv = fromPresheafComparisonInv alpha M := sorry

/-- The sheafified tensor-presheaf comparison is available to typeclass search as an
isomorphism. -/
@[stacks 01BH "sheafified tensor comparison is an isomorphism"]
noncomputable instance fromPresheafComparison_isIso (alpha : R →+* X.globalSectionsRing)
    (M : ModuleCat.{u} R) : IsIso (fromPresheafComparison alpha M) := sorry

/-- The sheafified tensor comparison is natural in the input module. -/
@[stacks 01BH "sheafified tensor comparison naturality"]
theorem fromPresheafComparison_naturality (alpha : R →+* X.globalSectionsRing)
    {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (sheafFunctor alpha).map f ≫ fromPresheafComparison alpha N =
      fromPresheafComparison alpha M ≫ (functor alpha).map f := sorry

/-- The explicit inverse tensor comparison is natural in the input module. -/
@[reassoc, stacks 01BH "inverse sheafified tensor comparison naturality"]
theorem fromPresheafComparisonInv_naturality (alpha : R →+* X.globalSectionsRing)
    {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (functor alpha).map f ≫ fromPresheafComparisonInv alpha N =
      fromPresheafComparisonInv alpha M ≫ (sheafFunctor alpha).map f := sorry

/-- The natural comparison from the sheafified tensor model to the associated-module functor. -/
@[stacks 01BH "natural sheafified tensor comparison"]
noncomputable def sheafComparison (alpha : R →+* X.globalSectionsRing) :
    sheafFunctor alpha ⟶ functor alpha where
  app M := fromPresheafComparison alpha M
  naturality := fun {_ _} f => fromPresheafComparison_naturality alpha f

/-- The explicit inverse natural comparison from associated module sheaves to their sheafified
tensor models. -/
@[stacks 01BH "inverse natural sheafified tensor comparison"]
noncomputable def sheafComparisonInv (alpha : R →+* X.globalSectionsRing) :
    functor alpha ⟶ sheafFunctor alpha where
  app M := fromPresheafComparisonInv alpha M
  naturality := fun {_ _} f => fromPresheafComparisonInv_naturality alpha f

/-- The natural tensor comparison followed by its explicit inverse is the identity. -/
@[simp, stacks 01BH "natural tensor comparison forward-inverse law"]
theorem sheafComparison_hom_inv_id (alpha : R →+* X.globalSectionsRing) :
    sheafComparison alpha ≫ sheafComparisonInv alpha = 𝟙 _ := sorry

/-- The explicit inverse natural tensor comparison followed by the comparison is the identity. -/
@[simp, stacks 01BH "natural tensor comparison inverse-forward law"]
theorem sheafComparison_inv_hom_id (alpha : R →+* X.globalSectionsRing) :
    sheafComparisonInv alpha ≫ sheafComparison alpha = 𝟙 _ := sorry

/-- Lemma 17.10.5 (01BH) (2), functorial form: sheafifying
`M ↦ (U ↦ O_X(U) ⊗_R M)` gives the associated-module functor. -/
@[stacks 01BH "(2), functorial form"]
noncomputable def associatedIso (alpha : R →+* X.globalSectionsRing) :
    sheafFunctor alpha ≅ functor alpha where
  hom := sheafComparison alpha
  inv := sheafComparisonInv alpha
  hom_inv_id := sheafComparison_hom_inv_id alpha
  inv_hom_id := sheafComparison_inv_hom_id alpha

/-- The forward map of `associatedIso` is the natural tensor comparison. -/
@[simp, stacks 01BH "associated tensor-model isomorphism hom"]
theorem associatedIso_hom (alpha : R →+* X.globalSectionsRing) :
    (associatedIso alpha).hom = sheafComparison alpha := sorry

/-- The inverse map of `associatedIso` is the explicit inverse natural comparison. -/
@[simp, stacks 01BH "associated tensor-model isomorphism inverse"]
theorem associatedIso_inv (alpha : R →+* X.globalSectionsRing) :
    (associatedIso alpha).inv = sheafComparisonInv alpha := sorry

/-- The natural tensor-model comparison is available to typeclass search as an isomorphism. -/
@[stacks 01BH "natural tensor-model comparison is an isomorphism"]
noncomputable instance sheafComparisonIsIso (alpha : R →+* X.globalSectionsRing) :
    IsIso (sheafComparison alpha) := sorry

/-- Lemma 17.10.5 (2) (01BH): the associated module sheaf is canonically isomorphic to the
sheafification of `U ↦ O_X(U) ⊗_R M`. -/
@[stacks 01BH "(2)"]
noncomputable def fromPresheafIso (alpha : R →+* X.globalSectionsRing)
    (M : ModuleCat.{u} R) : obj alpha M ≅ fromPresheaf alpha M :=
  (fromPresheafComparisonIso alpha M).symm

/-- The forward map of `fromPresheafIso` is the explicit inverse tensor comparison. -/
@[simp, stacks 01BH "associated-to-tensor isomorphism hom"]
theorem fromPresheafIso_hom (alpha : R →+* X.globalSectionsRing)
    (M : ModuleCat.{u} R) :
    (fromPresheafIso alpha M).hom = fromPresheafComparisonInv alpha M := sorry

/-- The inverse map of `fromPresheafIso` is the canonical tensor comparison. -/
@[simp, stacks 01BH "associated-to-tensor isomorphism inverse"]
theorem fromPresheafIso_inv (alpha : R →+* X.globalSectionsRing)
    (M : ModuleCat.{u} R) :
    (fromPresheafIso alpha M).inv = fromPresheafComparison alpha M := sorry

end AlgebraicGeometry.RingedSpace.Module.Associated
