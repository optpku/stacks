/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Equivalence
public import ReasLib.Algebra.Category.ModuleCat.SquareZero
public import ReasLib.Algebra.Category.ModuleCat.DualNumber.SquareZero

@[expose] public section

/-!
# Dual-number modules as square-zero differentials

A module over `R[ε]` is equivalently an `R`-module with a square-zero endomorphism. This file
builds that equivalence using the algebra-independent API in `ModuleCat.SquareZero`.
-/

universe u v

open CategoryTheory
open scoped DualNumber

namespace ModuleCat

namespace DualNumber.Differential

variable {R : Type u} [CommRing R]

/-- A dual-number module as an `R`-module with square-zero differential given by multiplication
by `ε`. -/
@[stacks 05CS "dual-number module as a differential"]
noncomputable def toObj (M : ModuleCat.{v} R[ε]) : ModuleCat.SquareZero.{v} R :=
  SquareZero.of (restrict M) (restrictedEpsEnd M) (restrictedEpsEnd_sq M)

/-- The restricted map underlying a dual-number morphism commutes with the corresponding
square-zero endomorphisms. -/
theorem toMap_comm {M N : ModuleCat.{v} R[ε]} (f : M ⟶ N) :
    restrictFunctor.map f ≫ SquareZero.d (toObj N) =
      SquareZero.d (toObj M) ≫ restrictFunctor.map f := by
  exact restrictedEpsEnd_naturality f

/-- A morphism of dual-number modules as a morphism commuting with the associated square-zero
differentials. -/
@[stacks 05CS "dual-number morphism as a differential morphism"]
noncomputable def toMap {M N : ModuleCat.{v} R[ε]} (f : M ⟶ N) :
    toObj M ⟶ toObj N :=
  SquareZero.homMk (restrictFunctor.map f) (toMap_comm f)

/-- The differential model has the restricted module as its unique component. -/
@[simp]
theorem toObj_carrier (M : ModuleCat.{v} R[ε]) :
    (toObj M).carrier = restrict M := rfl

/-- The differential in the differential model is restricted multiplication by `ε`. -/
@[simp]
theorem toObj_d (M : ModuleCat.{v} R[ε]) :
    SquareZero.d (toObj M) = restrictedEpsEnd M := rfl

/-- The unique component of the differential-model map is the restricted original map. -/
@[simp]
theorem toMap_component {M N : ModuleCat.{v} R[ε]} (f : M ⟶ N) :
    SquareZero.component (toMap f) = restrictFunctor.map f := by
  simp only [toMap, SquareZero.component, SquareZero.homMk, SquareZero.homMkApp,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- The differential-model map associated to an identity is an identity. -/
@[simp]
theorem toMap_id (M : ModuleCat.{v} R[ε]) :
    toMap (𝟙 M) = 𝟙 (toObj M) := by
  apply HomologicalComplex.hom_ext
  intro i
  cases i
  change SquareZero.component (toMap (𝟙 M)) = 𝟙 (restrict M)
  rw [toMap_component]
  exact restrictFunctor.map_id M

/-- The differential-model map preserves composition. -/
@[simp]
theorem toMap_comp {M N P : ModuleCat.{v} R[ε]} (f : M ⟶ N) (g : N ⟶ P) :
    toMap (f ≫ g) = toMap f ≫ toMap g := by
  apply HomologicalComplex.hom_ext
  intro i
  cases i
  change SquareZero.component (toMap (f ≫ g)) =
    SquareZero.component (toMap f) ≫ SquareZero.component (toMap g)
  rw [toMap_component, toMap_component, toMap_component]
  exact restrictFunctor.map_comp f g

/-- The functor from dual-number modules to square-zero differentials. -/
@[stacks 05CS "dual-number differential functor"]
noncomputable def toFunctor : ModuleCat.{v} R[ε] ⥤ ModuleCat.SquareZero.{v} R where
  obj := toObj
  map := toMap
  map_id := toMap_id
  map_comp := toMap_comp

/-- A square-zero differential as a module over the dual numbers. -/
@[stacks 05CS "differential as a dual-number module"]
def ofObj (K : ModuleCat.SquareZero.{v} R) : ModuleCat.{v} R[ε] :=
  ofSquareZero (SquareZero.d K).hom (SquareZero.d_hom_sq K)

/-- The commutation relation on underlying linear maps for a morphism of square-zero
differentials. -/
theorem ofMap_comm {K L : ModuleCat.SquareZero.{v} R} (f : K ⟶ L) :
    (SquareZero.component f).hom.comp (SquareZero.d K).hom =
      (SquareZero.d L).hom.comp (SquareZero.component f).hom := by
  exact congrArg ModuleCat.Hom.hom (f.comm PUnit.unit PUnit.unit).symm

/-- A morphism of square-zero differentials as a morphism of dual-number modules. -/
@[stacks 05CS "differential morphism as a dual-number morphism"]
def ofMap {K L : ModuleCat.SquareZero.{v} R} (f : K ⟶ L) : ofObj K ⟶ ofObj L :=
  ofSquareZeroMap (SquareZero.d K).hom (SquareZero.d_hom_sq K)
    (SquareZero.d L).hom (SquareZero.d_hom_sq L)
    (SquareZero.component f).hom (ofMap_comm f)

/-- The morphism reconstructed from a differential has the unique component as its underlying
map. -/
@[simp]
theorem ofMap_apply {K L : ModuleCat.SquareZero.{v} R} (f : K ⟶ L)
    (x : K.carrier) :
    (ofMap f).hom x = (SquareZero.component f).hom x := rfl

/-- Passing an identity differential morphism to dual-number modules gives an identity. -/
@[simp]
theorem ofMap_id (K : ModuleCat.SquareZero.{v} R) :
    ofMap (𝟙 K) = 𝟙 (ofObj K) := by
  ext x
  rfl

/-- Passing differential morphisms to dual-number modules preserves composition. -/
@[simp]
theorem ofMap_comp {K L N : ModuleCat.SquareZero.{v} R} (f : K ⟶ L) (g : L ⟶ N) :
    ofMap (f ≫ g) = ofMap f ≫ ofMap g := by
  ext x
  rfl

/-- The functor from square-zero differentials to dual-number modules. -/
@[stacks 05CS "differential dual-number functor"]
def ofFunctor : ModuleCat.SquareZero.{v} R ⥤ ModuleCat.{v} R[ε] where
  obj := ofObj
  map := ofMap
  map_id := ofMap_id
  map_comp := ofMap_comp

/-- The dual-number scalar action reconstructed from multiplication by `ε`, expressed on the
original carrier. -/
@[stacks 05CS "reconstructed dual-number action"]
noncomputable def reconstructedSmul (M : ModuleCat.{v} R[ε]) (a : R[ε]) (x : M) : M :=
  ((toFunctor ⋙ ofFunctor).obj M).isModule.toDistribMulAction.toMulAction.toSMul.smul a x

/-- The identity additive equivalence respects the original and reconstructed dual-number
actions. -/
theorem unitEquiv_map_smul (M : ModuleCat.{v} R[ε]) (a : R[ε]) (x : M) :
    AddEquiv.refl M (a • x) = reconstructedSmul M a x := by
  change Reconstruction.originalSmul M a x =
    (a • (show ofSquareZero (restrictedEpsEnd M).hom
      (restrictedEpsEnd_hom_sq M) from x) :
      ofSquareZero (restrictedEpsEnd M).hom (restrictedEpsEnd_hom_sq M))
  exact (Reconstruction.smul M a x).symm

/-- The explicit linear equivalence from a dual-number module to the module reconstructed from
its square-zero differential. -/
@[stacks 05CS "dual-number differential reconstruction"]
noncomputable def unitEquiv (M : ModuleCat.{v} R[ε]) :
    M ≃ₗ[R[ε]] ((toFunctor ⋙ ofFunctor).obj M : Type v) :=
  { __ := AddEquiv.refl M
    map_smul' := unitEquiv_map_smul M }

/-- The component of the reconstruction isomorphism on a dual-number module. -/
noncomputable def unitApp (M : ModuleCat.{v} R[ε]) :
    M ≅ (toFunctor ⋙ ofFunctor).obj M :=
  (unitEquiv M).toModuleIso

/-- The reconstruction components are natural in the dual-number module. -/
theorem unitApp_naturality {M N : ModuleCat.{v} R[ε]} (f : M ⟶ N) :
    f ≫ (unitApp N).hom =
      (unitApp M).hom ≫ (toFunctor ⋙ ofFunctor).map f := by
  ext x
  change f.hom x = (SquareZero.component (toMap f)).hom x
  rw [toMap_component]
  rfl

/-- Reconstructing a dual-number module from its differential is naturally isomorphic to the
original module. -/
@[stacks 05CS "dual-number differential unit"]
noncomputable def unitIso : 𝟭 (ModuleCat.{v} R[ε]) ≅ toFunctor ⋙ ofFunctor :=
  NatIso.ofComponents unitApp unitApp_naturality

/-- The unit natural isomorphism has the named reconstruction component. -/
@[simp]
theorem unitIso_hom_app (M : ModuleCat.{v} R[ε]) :
    unitIso.hom.app M = (unitApp M).hom := rfl

/-- The unique component of the morphism from a reconstructed differential to the original
differential. -/
noncomputable def counitHomComponent (K : ModuleCat.SquareZero.{v} R) :
    (toObj (ofObj K)).carrier ⟶ K.carrier :=
  (restrictIso (SquareZero.d K).hom (SquareZero.d_hom_sq K)).hom

/-- The unique component of the inverse morphism from a differential to its reconstruction. -/
noncomputable def counitInvComponent (K : ModuleCat.SquareZero.{v} R) :
    K.carrier ⟶ (toObj (ofObj K)).carrier :=
  (restrictIso (SquareZero.d K).hom (SquareZero.d_hom_sq K)).inv

/-- The forward counit component commutes with the square-zero endomorphisms. -/
theorem counitHomComponent_comm (K : ModuleCat.SquareZero.{v} R) :
    counitHomComponent K ≫ SquareZero.d K =
      SquareZero.d (toObj (ofObj K)) ≫ counitHomComponent K := by
  ext x
  change (SquareZero.d K).hom x =
    (restrictedEpsEnd (ofSquareZero (SquareZero.d K).hom (SquareZero.d_hom_sq K))).hom x
  exact (restrictedEpsEnd_apply_ofSquareZero (SquareZero.d K).hom
    (SquareZero.d_hom_sq K) x).symm

/-- The inverse counit component commutes with the square-zero endomorphisms. -/
theorem counitInvComponent_comm (K : ModuleCat.SquareZero.{v} R) :
    counitInvComponent K ≫ SquareZero.d (toObj (ofObj K)) =
      SquareZero.d K ≫ counitInvComponent K := by
  ext x
  change
    (restrictedEpsEnd (ofSquareZero (SquareZero.d K).hom (SquareZero.d_hom_sq K))).hom x =
      (SquareZero.d K).hom x
  exact restrictedEpsEnd_apply_ofSquareZero (SquareZero.d K).hom
    (SquareZero.d_hom_sq K) x

/-- The forward morphism from the reconstructed differential to the original one. -/
noncomputable def counitHom (K : ModuleCat.SquareZero.{v} R) : toObj (ofObj K) ⟶ K :=
  SquareZero.homMk (counitHomComponent K) (counitHomComponent_comm K)

/-- The inverse morphism from a differential to its reconstruction. -/
noncomputable def counitInv (K : ModuleCat.SquareZero.{v} R) : K ⟶ toObj (ofObj K) :=
  SquareZero.homMk (counitInvComponent K) (counitInvComponent_comm K)

/-- The forward counit morphism has the named unique component. -/
@[simp]
theorem counitHom_component (K : ModuleCat.SquareZero.{v} R) :
    SquareZero.component (counitHom K) = counitHomComponent K := by
  simp only [counitHom, SquareZero.component, SquareZero.homMk, SquareZero.homMkApp,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- The inverse counit morphism has the named unique component. -/
@[simp]
theorem counitInv_component (K : ModuleCat.SquareZero.{v} R) :
    SquareZero.component (counitInv K) = counitInvComponent K := by
  simp only [counitInv, SquareZero.component, SquareZero.homMk, SquareZero.homMkApp,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- The forward and inverse counit morphisms compose to the identity on the reconstruction. -/
theorem counit_hom_inv_id (K : ModuleCat.SquareZero.{v} R) :
    counitHom K ≫ counitInv K = 𝟙 (toObj (ofObj K)) := by
  apply HomologicalComplex.hom_ext
  intro i
  cases i
  change SquareZero.component (counitHom K) ≫ SquareZero.component (counitInv K) =
    𝟙 ((toObj (ofObj K)).carrier)
  rw [counitHom_component, counitInv_component]
  ext x
  rfl

/-- The inverse and forward counit morphisms compose to the identity on the original complex. -/
theorem counit_inv_hom_id (K : ModuleCat.SquareZero.{v} R) :
    counitInv K ≫ counitHom K = 𝟙 K := by
  apply HomologicalComplex.hom_ext
  intro i
  cases i
  change SquareZero.component (counitInv K) ≫ SquareZero.component (counitHom K) =
    𝟙 K.carrier
  rw [counitHom_component, counitInv_component]
  ext x
  rfl

/-- The component identifying a reconstructed square-zero complex with the original complex. -/
noncomputable def counitApp (K : ModuleCat.SquareZero.{v} R) :
    (ofFunctor ⋙ toFunctor).obj K ≅ K where
  hom := counitHom K
  inv := counitInv K
  hom_inv_id := counit_hom_inv_id K
  inv_hom_id := counit_inv_hom_id K

/-- The differential reconstruction components are natural. -/
theorem counitApp_naturality {K L : ModuleCat.SquareZero.{v} R} (f : K ⟶ L) :
    (ofFunctor ⋙ toFunctor).map f ≫ (counitApp L).hom =
      (counitApp K).hom ≫ f := by
  apply HomologicalComplex.hom_ext
  intro i
  cases i
  change SquareZero.component (toMap (ofMap f)) ≫ SquareZero.component (counitHom L) =
    SquareZero.component (counitHom K) ≫ SquareZero.component f
  rw [toMap_component, counitHom_component, counitHom_component]
  ext x
  rfl

/-- Reconstructing a square-zero differential from its dual-number module is naturally
isomorphic to the original differential. -/
@[stacks 05CS "dual-number differential counit"]
noncomputable def counitIso :
    ofFunctor ⋙ toFunctor ≅ 𝟭 (ModuleCat.SquareZero.{v} R) :=
  NatIso.ofComponents counitApp counitApp_naturality

/-- The counit natural isomorphism has the named reconstruction component. -/
@[simp]
theorem counitIso_hom_app (K : ModuleCat.SquareZero.{v} R) :
    counitIso.hom.app K = (counitApp K).hom := rfl

/-- The named unit and counit satisfy the triangle identity for the forward functor. -/
theorem triangle (M : ModuleCat.{v} R[ε]) :
    toFunctor.map (unitIso.hom.app M) ≫
      counitIso.hom.app (toFunctor.obj M) = 𝟙 (toFunctor.obj M) := by
  apply HomologicalComplex.hom_ext
  intro i
  cases i
  change SquareZero.component (toMap (unitApp M).hom) ≫
    SquareZero.component (counitHom (toObj M)) = 𝟙 (toObj M).carrier
  ext x
  rfl

/-- The category of modules over the dual numbers is canonically equivalent to the category of
modules equipped with a square-zero endomorphism. -/
@[stacks 05CS "dual-number differential equivalence"]
noncomputable def equivalence : ModuleCat.{v} R[ε] ≌ ModuleCat.SquareZero.{v} R where
  functor := toFunctor
  inverse := ofFunctor
  unitIso := unitIso
  counitIso := counitIso
  functor_unitIso_comp := triangle

end DualNumber.Differential

end ModuleCat
