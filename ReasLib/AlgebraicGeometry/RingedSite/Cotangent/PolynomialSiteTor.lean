/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.LeftDerived
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Tensor
public import ReasLib.AlgebraicGeometry.RingedSite.Cotangent.PolynomialSiteVanishing

/-!
# Tor sheaves of the kernel ideal on the polynomial site

The sheaf `Tor_n^O(𝒥, underline{B})` on `C_{B/A}`, obtained objectwise as
left-derived extension of scalars of `Ker(P ⟶ B)` along `P ⟶ B`.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Limits
open HomologicalComplex
open scoped TensorProduct

noncomputable section

universe u

namespace CommAlgCat.Over.Polynomial.Site

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The objectwise derived scalar extension `Tor_n^P(Ker(P ⟶ B), B)`, in the presence of the
induced `P`-algebra structure on `B`. -/
def kernelTorObjWith (n : ℕ) (X : Algebra.PolynomialOver A B) [Algebra X.obj.left B] :
    ModuleCat.{u} B :=
  ((ModuleCat.extendScalars (algebraMap X.obj.left B)).leftDerived n).obj
    (ModuleCat.of X.obj.left (RingHom.ker (algebraMap X.obj.left B)))

/-- The objectwise derived scalar extension `Tor_n^P(Ker(P ⟶ B), B)`. -/
def kernelTorObj (n : ℕ) (X : Algebra.PolynomialOver A B) : ModuleCat.{u} B :=
  @kernelTorObjWith A B _ _ _ n X (algebraToBase X)

/-- Unfolding `kernelTorObj` recovers the unbundled left-derived extension of scalars. -/
theorem kernelTorObj_eq (n : ℕ) (X : Algebra.PolynomialOver A B) :
    kernelTorObj n X = @kernelTorObjWith A B _ _ _ n X (algebraToBase X) :=
  rfl

/-- The `P`-linear map `Ker(P ⟶ B) ⟶ Ker(P' ⟶ B)` induced by a morphism of polynomial arrows,
after restriction of scalars along `P ⟶ P'`. -/
def kernelRestrictMapWith {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y)
    [Algebra X.obj.left B] [Algebra Y.obj.left B] [Algebra X.obj.left Y.obj.left]
    [IsScalarTower X.obj.left Y.obj.left B] :
    ModuleCat.of X.obj.left (RingHom.ker (algebraMap X.obj.left B)) ⟶
      (ModuleCat.restrictScalars (algebraMap X.obj.left Y.obj.left)).obj
        (ModuleCat.of Y.obj.left (RingHom.ker (algebraMap Y.obj.left B))) :=
  ModuleCat.semilinearMapAddEquiv (algebraMap X.obj.left Y.obj.left)
      (ModuleCat.of X.obj.left (RingHom.ker (algebraMap X.obj.left B)))
      (ModuleCat.of Y.obj.left (RingHom.ker (algebraMap Y.obj.left B)))
    { toFun := fun j ↦
        ⟨algebraMap X.obj.left Y.obj.left (j : X.obj.left), kernel_le_comapWith f j.2⟩
      map_add' := sorry
      map_smul' := sorry }

/-- Unfolding `kernelRestrictMapWith` recovers the underlying ring map on kernels. -/
theorem kernelRestrictMapWith_apply {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y)
    [Algebra X.obj.left B] [Algebra Y.obj.left B] [Algebra X.obj.left Y.obj.left]
    [IsScalarTower X.obj.left Y.obj.left B]
    (j : RingHom.ker (algebraMap X.obj.left B)) :
    kernelRestrictMapWith f j =
      ⟨algebraMap X.obj.left Y.obj.left (j : X.obj.left), kernel_le_comapWith f j.2⟩ :=
  sorry

/-- The map on `Tor_n^P(Ker(P ⟶ B), B)` induced by a morphism of polynomial arrows, in the
presence of the induced algebra structures. -/
def kernelTorMapWith (n : ℕ) {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y)
    [Algebra X.obj.left B] [Algebra Y.obj.left B] [Algebra X.obj.left Y.obj.left]
    [IsScalarTower A X.obj.left Y.obj.left]
    [IsScalarTower X.obj.left Y.obj.left B] :
    kernelTorObjWith n X ⟶ kernelTorObjWith n Y :=
  eqToHom
      (congrArg
        (fun ψ : X.obj.left →+* B ↦
          ((ModuleCat.extendScalars ψ).leftDerived n).obj
            (ModuleCat.of X.obj.left (RingHom.ker (algebraMap X.obj.left B))))
        (IsScalarTower.algebraMap_eq X.obj.left Y.obj.left B)) ≫
    (NatTrans.leftDerived
        (ModuleCat.extendScalarsComp (algebraMap X.obj.left Y.obj.left)
          (algebraMap Y.obj.left B)).hom n).app
      (ModuleCat.of X.obj.left (RingHom.ker (algebraMap X.obj.left B))) ≫
    leftDerivedCompToPostcomposed (algebraMap X.obj.left Y.obj.left)
      (algebraMap Y.obj.left B) n
      (ModuleCat.of X.obj.left (RingHom.ker (algebraMap X.obj.left B))) ≫
    ((ModuleCat.extendScalars (algebraMap Y.obj.left B)).leftDerived n).map
      ((ModuleCat.extendScalars (algebraMap X.obj.left Y.obj.left)).map (kernelRestrictMapWith f) ≫
        (ModuleCat.extendRestrictScalarsAdj (algebraMap X.obj.left Y.obj.left)).counit.app
          (ModuleCat.of Y.obj.left (RingHom.ker (algebraMap Y.obj.left B))))

/-- The map on `Tor_n^P(Ker(P ⟶ B), B)` induced by a morphism of polynomial arrows over `B`. -/
def kernelTorMap (n : ℕ) {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y) :
    kernelTorObj n X ⟶ kernelTorObj n Y :=
  @kernelTorMapWith A B _ _ _ n X Y f (algebraToBase X) (algebraToBase Y) (algebraOfHom f)
    (algebraOfHom_isScalarTower f) (toBase_isScalarTower f)

/-- Unfolding `kernelTorMap` recovers the change-of-rings comparison on left-derived
extension of scalars. -/
theorem kernelTorMap_eq (n : ℕ) {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y) :
    kernelTorMap n f =
      @kernelTorMapWith A B _ _ _ n X Y f (algebraToBase X) (algebraToBase Y) (algebraOfHom f)
        (algebraOfHom_isScalarTower f) (toBase_isScalarTower f) :=
  sorry

/-- Identity morphisms act as the identity on objectwise Tor. -/
theorem kernelTorMap_id (n : ℕ) (X : Algebra.PolynomialOver A B) :
    kernelTorMap n (𝟙 X) = 𝟙 (kernelTorObj n X) :=
  sorry

/-- Composition of polynomial-arrow morphisms maps to composition of objectwise Tor maps. -/
theorem kernelTorMap_comp (n : ℕ) {X Y Z : Algebra.PolynomialOver A B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    kernelTorMap n (f ≫ g) = kernelTorMap n f ≫ kernelTorMap n g :=
  sorry

variable (A B) in
/-- The covariant functor of objectwise `Tor_n^O(𝒥, underline{B})` on polynomial arrows
`P ⟶ B`. -/
def kernelTorCov (n : ℕ) : Algebra.PolynomialOver A B ⥤ ModuleCat.{u} B where
  obj := kernelTorObj n
  map f := kernelTorMap n f
  map_id X := kernelTorMap_id n X
  map_comp f g := kernelTorMap_comp n f g

/-- Objects of `kernelTorCov` are the objectwise Tor modules of the corresponding polynomial
arrow. -/
theorem kernelTorCov_obj (n : ℕ) (X : Algebra.PolynomialOver A B) :
    (kernelTorCov A B n).obj X = kernelTorObj n X :=
  sorry

variable (A B) in
/-- The sheaf `Tor_n^O(𝒥, underline{B})` on `C_{B/A}`, as a functor
`(PolynomialSite A B)ᵒᵖ ⥤ ModuleCat B`. -/
def kernelTorSheaf (n : ℕ) : (Algebra.PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B :=
  unopUnop (Algebra.PolynomialOver A B) ⋙ kernelTorCov A B n

/-- Evaluating `kernelTorSheaf` on a double-opposite polynomial arrow recovers `kernelTorObj`. -/
theorem kernelTorSheaf_obj (n : ℕ) (X : (Algebra.PolynomialSite A B)ᵒᵖ) :
    (kernelTorSheaf A B n).obj X = kernelTorObj n (unop (unop X)) :=
  sorry

/-- `kernelTorSheaf` is precomposition of `kernelTorCov` with the double-opposite equivalence. -/
theorem kernelTorSheaf_eq (n : ℕ) :
    kernelTorSheaf A B n = unopUnop (Algebra.PolynomialOver A B) ⋙ kernelTorCov A B n :=
  sorry

/-- Components of `kernelTorSheaf` on morphisms are `kernelTorMap` of the underlying polynomial
arrow. -/
theorem kernelTorSheaf_map (n : ℕ) {X Y : (Algebra.PolynomialSite A B)ᵒᵖ} (f : X ⟶ Y) :
    (kernelTorSheaf A B n).map f = kernelTorMap n f.unop.unop :=
  sorry

/-- The canonical morphism `Tor_0^P(Ker(P ⟶ B), B) ⟶ J/J² ⊗_P B` obtained from
`leftDerivedZeroIsoSelf` and extension of scalars along `toCotangent`. -/
def kernelTorZeroHomWith (X : Algebra.PolynomialOver A B) [Algebra X.obj.left B] :
    kernelTorObjWith 0 X ⟶ conormalObjWith X :=
  ((ModuleCat.extendScalars (algebraMap X.obj.left B)).leftDerivedZeroIsoSelf).hom.app
      (ModuleCat.of X.obj.left (RingHom.ker (algebraMap X.obj.left B))) ≫
    (ModuleCat.extendScalars (algebraMap X.obj.left B)).map
      (ModuleCat.ofHom (RingHom.ker (algebraMap X.obj.left B)).toCotangent) ≫
    (ModuleCat.ExtendScalars.tensorIso
      (ModuleCat.of X.obj.left (RingHom.ker (algebraMap X.obj.left B)).Cotangent)).hom

/-- Products in the kernel vanish after tensoring with the target algebra. -/
theorem kernelTensor_product {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]
    (t : T) (x y : RingHom.ker (algebraMap R T)) :
    t ⊗ₜ[R] (x * y) = (0 : T ⊗[R] RingHom.ker (algebraMap R T)) := by
  have hxy : x * y = (x : R) • y := by ext; rfl
  rw [hxy, ← TensorProduct.smul_tmul, Algebra.smul_def, x.property, zero_mul,
    TensorProduct.zero_tmul]

/-- The inverse sends a pure tensor with a conormal class to the same kernel tensor.
It descends through the quotient because products of kernel elements tensor to zero. -/
def kernelTensorCotangentInv {R T : Type u} [CommRing R] [CommRing T] [Algebra R T] :
    T ⊗[R] (RingHom.ker (algebraMap R T)).Cotangent →ₗ[T]
      T ⊗[R] RingHom.ker (algebraMap R T) :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun t ↦ Ideal.Cotangent.lift (TensorProduct.mk R T _ t)
        (kernelTensor_product t)
      map_add' := by
        intro t t'
        apply LinearMap.ext
        intro q
        obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ q
        simp
      map_smul' := by
        intro t t'
        apply LinearMap.ext
        intro q
        obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ q
        simp [TensorProduct.smul_tmul'] }

/-- Tensoring the kernel-to-conormal quotient with the target algebra is an isomorphism.
No flatness or surjectivity assumption is needed for this degree-zero comparison. -/
def kernelTensorCotangentIso {R T : Type u} [CommRing R] [CommRing T] [Algebra R T] :
    ModuleCat.of T (T ⊗[R] RingHom.ker (algebraMap R T)) ≅
      ModuleCat.of T (T ⊗[R] (RingHom.ker (algebraMap R T)).Cotangent) :=
  LinearEquiv.toModuleIso
    { toLinearMap := (RingHom.ker (algebraMap R T)).toCotangent.baseChange T
      invFun := kernelTensorCotangentInv
      left_inv := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul t x => rfl
        | add x y hx hy =>
            change kernelTensorCotangentInv
              (((RingHom.ker (algebraMap R T)).toCotangent.baseChange T) (x + y)) = _
            rw [map_add, map_add]
            exact congrArg₂ (· + ·) hx hy
      right_inv := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul t q =>
            obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ q
            rfl
        | add x y hx hy =>
            change ((RingHom.ker (algebraMap R T)).toCotangent.baseChange T)
              (kernelTensorCotangentInv (x + y)) = _
            rw [map_add, map_add]
            exact congrArg₂ (· + ·) hx hy }

/-- The canonical morphism `kernelTorZeroHomWith` is an isomorphism. -/
instance kernelTorZeroHomWith_isIso (X : Algebra.PolynomialOver A B) [Algebra X.obj.left B] :
    IsIso (kernelTorZeroHomWith X) := by
  let F := ModuleCat.extendScalars (algebraMap X.obj.left B)
  let I := RingHom.ker (algebraMap X.obj.left B)
  have h : F.map (ModuleCat.ofHom I.toCotangent) =
      (ModuleCat.ExtendScalars.tensorIso (ModuleCat.of X.obj.left I)).hom ≫
        (kernelTensorCotangentIso (R := X.obj.left) (T := B)).hom ≫
        (ModuleCat.ExtendScalars.tensorIso (ModuleCat.of X.obj.left I.Cotangent)).inv := by
    apply (cancel_mono
      (ModuleCat.ExtendScalars.tensorIso (ModuleCat.of X.obj.left I.Cotangent)).hom).1
    simpa [F, kernelTensorCotangentIso] using
      (ModuleCat.ExtendScalars.tensorIso_naturality (ModuleCat.ofHom I.toCotangent))
  let e : kernelTorObjWith 0 X ≅ conormalObjWith X :=
    F.leftDerivedZeroIsoSelf.app (ModuleCat.of X.obj.left I) ≪≫
      ModuleCat.ExtendScalars.tensorIso (ModuleCat.of X.obj.left I) ≪≫
      kernelTensorCotangentIso
  have he : kernelTorZeroHomWith X = e.hom := by
    unfold kernelTorZeroHomWith
    dsimp only [F, I] at h
    rw [h]
    simp only [Category.assoc]
    erw [Iso.inv_hom_id, Category.comp_id]
    rfl
  rw [he]
  exact e.isIso_hom

/-- The objectwise identification `Tor_0^P(Ker(P ⟶ B), B) ≅ J/J² ⊗_P B`. -/
def kernelTorZeroIsoAppWith (X : Algebra.PolynomialOver A B) [Algebra X.obj.left B] :
    kernelTorObjWith 0 X ≅ conormalObjWith X :=
  asIso (kernelTorZeroHomWith X)

/-- The objectwise identification `Tor_0 ≅ 𝒥/𝒥²` of a polynomial arrow. -/
def kernelTorZeroIsoApp (X : Algebra.PolynomialOver A B) :
    kernelTorObj 0 X ≅ conormalObj X :=
  @kernelTorZeroIsoAppWith A B _ _ _ X (algebraToBase X)

/-- The forward morphism of `kernelTorZeroIsoAppWith` is `kernelTorZeroHomWith`. -/
theorem kernelTorZeroIsoAppWith_hom (X : Algebra.PolynomialOver A B) [Algebra X.obj.left B] :
    (kernelTorZeroIsoAppWith X).hom = kernelTorZeroHomWith X :=
  rfl

variable (A B) in
/-- The identification `Tor_0^O(𝒥, underline{B}) ≅ 𝒥/𝒥²` of sheaves on `C_{B/A}`. -/
def kernelTorZeroIso : kernelTorSheaf A B 0 ≅ conormalSheaf A B :=
  NatIso.ofComponents (fun X ↦ kernelTorZeroIsoApp (unop (unop X))) sorry

/-- Components of `kernelTorZeroIso` are the objectwise identifications `kernelTorZeroIsoApp`. -/
theorem kernelTorZeroIso_hom_app (X : (Algebra.PolynomialSite A B)ᵒᵖ) :
    (kernelTorZeroIso A B).hom.app X = (kernelTorZeroIsoApp (unop (unop X))).hom :=
  sorry

/-- Inverse components of `kernelTorZeroIso` are the objectwise inverse identifications. -/
theorem kernelTorZeroIso_inv_app (X : (Algebra.PolynomialSite A B)ᵒᵖ) :
    (kernelTorZeroIso A B).inv.app X = (kernelTorZeroIsoApp (unop (unop X))).inv :=
  sorry

end CommAlgCat.Over.Polynomial.Site
