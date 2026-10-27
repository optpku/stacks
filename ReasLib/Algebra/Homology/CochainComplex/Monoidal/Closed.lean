/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Adjunction.Additive
public import ReasLib.CategoryTheory.GradedObject.Monoidal.Closed
import Mathlib.Tactic.CrossRefAttribute

/-!
# Closed structure on integer cochain complexes

The internal Hom complex from `X` to `Y` has degree-`n` object
`∏ i, (X.X i ⟶[C] Y.X (i + n))`. Its differential is the graded commutator of
postcomposition by `Y.d` and precomposition by `X.d`. This file constructs the object and the
tensor/internal-Hom adjunction independently of rings, modules, sheaves, and bimodules.
-/

@[expose] public section

open CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v

namespace CategoryTheory.CochainComplex.InternalHom

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
variable [HasZeroObject C] [HasProductsOfShape ℤ C]
variable [∀ X Y : GradedObject ℤ C, GradedObject.HasTensor X Y]
variable [∀ X Y Z : GradedObject ℤ C, GradedObject.HasGoodTensor₁₂Tensor X Y Z]
variable [∀ X Y Z : GradedObject ℤ C, GradedObject.HasGoodTensorTensor₂₃ X Y Z]
variable [∀ X Y Z W : GradedObject ℤ C, GradedObject.HasTensor₄ObjExt X Y Z W]
variable [∀ X, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X)]
variable [∀ X, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X)]

/-- Reassociate the target differential degree in the internal Hom complex. -/
theorem postDegree (i n : ℤ) : i + n + 1 = i + (n + 1) := add_assoc i n 1

/-- Reassociate the source differential degree in the internal Hom complex. -/
theorem preDegree (i n : ℤ) : (i + 1) + n = i + (n + 1) := by omega

/-- The family whose product is degree `n` of the internal Hom complex. -/
noncomputable abbrev family (X Y : CochainComplex C ℤ) (n : ℤ) : ℤ → C :=
  GradedObject.InternalHom.family X.X Y.X n

/-- The underlying graded object of the internal Hom complex. -/
@[stacks 0FRS "underlying graded object of a cochain internal Hom"]
noncomputable abbrev gradedObj (X Y : CochainComplex C ℤ) : GradedObject ℤ C :=
  GradedObject.InternalHom.obj X.X Y.X

/-- Postcomposition by the target differential in one source degree. -/
noncomputable def postDifferential (X Y : CochainComplex C ℤ) (n i : ℤ) :
    gradedObj X Y n ⟶ (ihom (X.X i)).obj (Y.X (i + (n + 1))) :=
  Pi.π (family X Y n) i ≫
    (ihom (X.X i)).map (Y.d (i + n) (i + n + 1)) ≫
      eqToHom
        (congrArg (fun j ↦ (ihom (X.X i)).obj (Y.X j)) (postDegree i n))

/-- Precomposition by the source differential in one source degree. -/
noncomputable def preDifferential (X Y : CochainComplex C ℤ) (n i : ℤ) :
    gradedObj X Y n ⟶ (ihom (X.X i)).obj (Y.X (i + (n + 1))) :=
  CategoryTheory.MonoidalClosed.curry
    ((X.d i (i + 1) ▷ gradedObj X Y n) ≫
      (X.X (i + 1) ◁ Pi.π (family X Y n) (i + 1)) ≫
        (ihom.ev (X.X (i + 1))).app (Y.X ((i + 1) + n)) ≫
          eqToHom (congrArg Y.X (preDegree i n)))

/-- The graded-commutator differential on the internal Hom complex. -/
noncomputable def differential (X Y : CochainComplex C ℤ) (n : ℤ) :
    gradedObj X Y n ⟶ gradedObj X Y (n + 1) :=
  Pi.lift fun i ↦
    postDifferential X Y n i + (n + 1).negOnePow • preDifferential X Y n i

private def asCochain {B : C} (X Y : CochainComplex C ℤ) {n : ℤ}
    (a : B ⟶ gradedObj X Y n) :
    _root_.CochainComplex.HomComplex.Cochain
      (((tensorRight B).mapHomologicalComplex (.up ℤ)).obj X) Y n :=
  _root_.CochainComplex.HomComplex.Cochain.mk fun i j h ↦
    CategoryTheory.MonoidalClosed.uncurry (a ≫ Pi.π (family X Y n) i) ≫
      eqToHom (congrArg Y.X h)

private theorem asCochain_injective {B : C} (X Y : CochainComplex C ℤ) (n : ℤ) :
    Function.Injective (asCochain X Y : (B ⟶ gradedObj X Y n) → _) := by
  intro a b h
  apply Pi.hom_ext
  intro i
  apply CategoryTheory.MonoidalClosed.uncurry_injective
  simpa only [asCochain, _root_.CochainComplex.HomComplex.Cochain.mk_v,
    eqToHom_refl, Category.comp_id] using
      _root_.CochainComplex.HomComplex.Cochain.congr_v h i (i + n) rfl

private theorem asCochain_differential {B : C} (X Y : CochainComplex C ℤ) (n : ℤ)
    (a : B ⟶ gradedObj X Y n) :
    asCochain X Y (a ≫ differential X Y n) =
      _root_.CochainComplex.HomComplex.δ n (n + 1) (asCochain X Y a) := by
  apply _root_.CochainComplex.HomComplex.Cochain.ext
  intro i j h
  subst j
  rw [_root_.CochainComplex.HomComplex.δ_v _ _ rfl _ _ _ rfl
    (i + n) (i + 1) (by omega) rfl]
  simp only [asCochain, _root_.CochainComplex.HomComplex.Cochain.mk_v,
    eqToHom_refl, Category.comp_id, differential, Category.assoc, Pi.lift_π]
  simp only [Preadditive.comp_add, Linear.comp_units_smul]
  change ((ihom.adjunction (X.X i)).homAddEquiv B _).symm _ = _
  rw [map_add, Units.smul_def, map_zsmul]
  change CategoryTheory.MonoidalClosed.uncurry (a ≫ postDifferential X Y n i) +
    (n + 1).negOnePow • CategoryTheory.MonoidalClosed.uncurry
      (a ≫ preDifferential X Y n i) = _
  congr 1
  · simp only [postDifferential, Category.assoc]
    rw [← eqToHom_map (ihom (X.X i)) (congrArg Y.X (postDegree i n)),
      ← Functor.map_comp, ← Category.assoc,
      CategoryTheory.MonoidalClosed.uncurry_natural_right,
      HomologicalComplex.d_comp_eqToHom]
    all_goals simp only [ComplexShape.up_Rel, add_assoc]
  · congr 1
    simp only [preDifferential, ← CategoryTheory.MonoidalClosed.curry_natural_left,
      CategoryTheory.MonoidalClosed.uncurry_curry,
      CategoryTheory.MonoidalClosed.uncurry_eq, Category.assoc,
      MonoidalCategory.whiskerLeft_comp]
    rw [MonoidalCategory.whisker_exchange_assoc]
    rw [CategoryTheory.MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
    rfl

/-- Consecutive internal-Hom differentials compose to zero. -/
theorem differential_sq (X Y : CochainComplex C ℤ) (n : ℤ) :
    differential X Y n ≫ differential X Y (n + 1) = 0 := by
  apply asCochain_injective X Y (n + 1 + 1)
  rw [asCochain_differential]
  have h := asCochain_differential X Y n (𝟙 (gradedObj X Y n))
  rw [Category.id_comp] at h
  rw [h, _root_.CochainComplex.HomComplex.δ_δ]
  apply _root_.CochainComplex.HomComplex.Cochain.ext
  intro i j h
  simp only [asCochain, _root_.CochainComplex.HomComplex.Cochain.mk_v,
    _root_.CochainComplex.HomComplex.Cochain.zero_v, zero_comp]
  change 0 = ((ihom.adjunction (X.X i)).homAddEquiv _ _).symm 0 ≫ _
  simp only [map_zero, zero_comp]

/-- The internal Hom complex with its explicit graded-commutator differential. -/
@[stacks 0FRS "cochain internal Hom object"]
noncomputable def obj (X Y : CochainComplex C ℤ) : CochainComplex C ℤ :=
  CochainComplex.of (gradedObj X Y) (differential X Y) (differential_sq X Y)

/-- Postcomposition by a cochain map on internal Hom complexes. -/
noncomputable def map (X : CochainComplex C ℤ) {Y Y' : CochainComplex C ℤ} (f : Y ⟶ Y') :
    obj X Y ⟶ obj X Y' where
  f n := GradedObject.InternalHom.map X.X f.f n
  comm' := by
    intro n m h
    obtain rfl : n + 1 = m := h
    apply Pi.hom_ext
    intro i
    simp only [obj, CochainComplex.of_d, differential, GradedObject.InternalHom.map, Category.assoc,
      Pi.lift_π, Pi.lift_π_assoc, Preadditive.comp_add, Preadditive.add_comp,
      Linear.comp_units_smul, Linear.units_smul_comp]
    congr 1
    · simp only [postDifferential, GradedObject.InternalHom.map, Category.assoc,
        Pi.lift_π_assoc, Pi.lift_π]
      rw [← Functor.map_comp_assoc, f.comm, Functor.map_comp]
      simp only [Category.assoc]
      congr 2
      exact eqToHom_naturality (fun j ↦ (ihom (X.X i)).map (f.f j))
        (postDegree i n)
    · simp only [preDifferential, GradedObject.InternalHom.map, Category.assoc,
        ← CategoryTheory.MonoidalClosed.curry_natural_left,
        ← CategoryTheory.MonoidalClosed.curry_natural_right,
        MonoidalCategory.whiskerLeft_comp, Pi.lift_π]
      congr 1
      apply congrArg CategoryTheory.MonoidalClosed.curry
      rw [← MonoidalCategory.whisker_exchange_assoc]
      simp only [← MonoidalCategory.whiskerLeft_comp_assoc, Pi.lift_π]
      simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
      rw [MonoidalCategory.whisker_exchange_assoc]
      rw [ihom.ev_naturality_assoc, ← MonoidalCategory.whisker_exchange_assoc]
      rw [eqToHom_naturality (fun j ↦ f.f j) (preDegree i n)]

/-- Internal Hom from a fixed cochain complex, functorial in the target complex. -/
@[stacks 0FRS "cochain internal Hom functor"]
noncomputable def functor (X : CochainComplex C ℤ) :
    CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj := obj X
  map := map X
  map_id := by
    intro Y
    ext n
    apply Pi.hom_ext
    intro i
    simp only [map, GradedObject.InternalHom.map, HomologicalComplex.id_f,
      Pi.lift_π, Functor.map_id, Category.comp_id, Category.id_comp]
  map_comp := by
    intro Y Y' Y'' f g
    ext n
    apply Pi.hom_ext
    intro i
    simp only [map, GradedObject.InternalHom.map, HomologicalComplex.comp_f,
      Pi.lift_π, Category.assoc, Pi.lift_π_assoc, Functor.map_comp]

private theorem curry_units_smul {A B D : C} (r : ℤˣ) (f : A ⊗ B ⟶ D) :
    CategoryTheory.MonoidalClosed.curry (r • f) =
      r • CategoryTheory.MonoidalClosed.curry f := by
  change (ihom.adjunction A).homAddEquiv B D ((r : ℤ) • f) =
    (r : ℤ) • (ihom.adjunction A).homAddEquiv B D f
  exact map_zsmul _ _ _

private theorem uncurry_units_smul {A B D : C} (r : ℤˣ) (f : B ⟶ (ihom A).obj D) :
    CategoryTheory.MonoidalClosed.uncurry (r • f) =
      r • CategoryTheory.MonoidalClosed.uncurry f := by
  change ((ihom.adjunction A).homAddEquiv B D).symm ((r : ℤ) • f) =
    (r : ℤ) • ((ihom.adjunction A).homAddEquiv B D).symm f
  exact map_zsmul _ _ _

private theorem ι_tensor_d (X Z : CochainComplex C ℤ) (i n : ℤ) :
    HomologicalComplex.ιTensorObj X Z i n (i + n) rfl ≫
      (X ⊗ Z).d (i + n) (i + (n + 1)) =
    (X.d i (i + 1) ▷ Z.X n) ≫
      HomologicalComplex.ιTensorObj X Z (i + 1) n (i + (n + 1)) (by omega) +
    i.negOnePow • (X.X i ◁ Z.d n (n + 1)) ≫
      HomologicalComplex.ιTensorObj X Z i (n + 1) (i + (n + 1)) rfl := by
  change HomologicalComplex.ιMapBifunctor X Z (curriedTensor C) (.up ℤ) _ _ _ _ ≫
    (HomologicalComplex.mapBifunctor X Z (curriedTensor C) (.up ℤ)).d _ _ = _
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ rfl _ _ (by dsimp; omega),
    HomologicalComplex.mapBifunctor.d₂_eq X Z (curriedTensor C) (.up ℤ) i
      (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl) (i + (n + 1)) rfl]
  change (1 : ℤˣ) • _ + _ = _
  rw [one_smul]
  rfl

/-- Curry a cochain map into the explicit internal Hom complex. -/
noncomputable def curry {X Y Z : CochainComplex C ℤ} (f : X ⊗ Z ⟶ Y) :
    Z ⟶ obj X Y where
  f n := Pi.lift fun i ↦ (i * n).negOnePow •
    CategoryTheory.MonoidalClosed.curry
      (HomologicalComplex.ιTensorObj X Z i n (i + n) rfl ≫ f.f (i + n))
  comm' := by
    intro n m h
    obtain rfl : n + 1 = m := h
    apply asCochain_injective X Y (n + 1)
    simp only [obj, CochainComplex.of_d]
    rw [asCochain_differential]
    apply _root_.CochainComplex.HomComplex.Cochain.ext
    intro i j h
    subst j
    rw [_root_.CochainComplex.HomComplex.δ_v _ _ rfl _ _ _ rfl
      (i + n) (i + 1) (by omega) rfl]
    simp only [asCochain, _root_.CochainComplex.HomComplex.Cochain.mk_v,
      Category.assoc, Pi.lift_π, eqToHom_refl, Category.comp_id,
      ← CategoryTheory.MonoidalClosed.curry_natural_left,
      CategoryTheory.MonoidalClosed.uncurry_curry]
    simp only [Linear.comp_units_smul, uncurry_units_smul,
      CategoryTheory.MonoidalClosed.uncurry_curry,
      CategoryTheory.MonoidalClosed.uncurry_natural_left]
    simp only [Linear.units_smul_comp, Linear.comp_units_smul, Category.assoc]
    rw [f.comm]
    rw [← Category.assoc, ι_tensor_d, Preadditive.add_comp,
      Linear.units_smul_comp, smul_add]
    rw [eqToHom_naturality (fun j ↦ f.f j) (preDegree i n)]
    simp only [Linear.units_smul_comp, Category.assoc, smul_smul]
    have hι : HomologicalComplex.ιTensorObj X Z (i + 1) n (i + 1 + n) rfl ≫
        eqToHom (congrArg (X ⊗ Z).X (preDegree i n)) =
        HomologicalComplex.ιTensorObj X Z (i + 1) n (i + (n + 1)) (by omega) := by
      have hh (k : ℤ) (h : i + 1 + n = k) :
          HomologicalComplex.ιTensorObj X Z (i + 1) n (i + 1 + n) rfl ≫
            eqToHom (congrArg (X ⊗ Z).X h) =
            HomologicalComplex.ιTensorObj X Z (i + 1) n k h := by
        subst k
        simp only [eqToHom_refl, Category.comp_id]
      exact hh _ _
    rw [← Category.assoc (HomologicalComplex.ιTensorObj X Z (i + 1) n _ _), hι]
    have hsign : (n + 1).negOnePow * ((i + 1) * n).negOnePow = -(i * n).negOnePow := by
      rw [← Int.negOnePow_add]
      have hh : n + 1 + (i + 1) * n = i * n + 1 + 2 * n := by ring
      rw [hh, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one, Int.negOnePow_succ]
    rw [hsign, Units.neg_smul]
    have hsign' : (i * n).negOnePow * i.negOnePow = (i * (n + 1)).negOnePow := by
      rw [← Int.negOnePow_add, mul_add, mul_one]
    rw [hsign']
    change _ + _ + -((i * n).negOnePow •
      (X.d i (i + 1) ▷ Z.X n) ≫
        HomologicalComplex.ιTensorObj X Z (i + 1) n _ _ ≫ f.f _) = _
    abel

/-- The homogeneous projection of cochain currying includes the Koszul sign. -/
@[reassoc (attr := simp)]
theorem curry_f_π {X Y Z : CochainComplex C ℤ} (f : X ⊗ Z ⟶ Y) (n i : ℤ) :
    (curry f).f n ≫ Pi.π (family X Y n) i =
      (i * n).negOnePow • CategoryTheory.MonoidalClosed.curry
        (HomologicalComplex.ιTensorObj X Z i n (i + n) rfl ≫ f.f (i + n)) := by
  apply Pi.lift_π

private def uncurryComponent {X Y Z : CochainComplex C ℤ} (f : Z ⟶ obj X Y)
    (k : ℤ) : (X ⊗ Z).X k ⟶ Y.X k :=
  GradedObject.Monoidal.tensorObjDesc fun i n h ↦
    (i * n).negOnePow •
      ((X.X i ◁ f.f n) ≫
        (X.X i ◁ Pi.π (family X Y n) i) ≫
          (ihom.ev (X.X i)).app (Y.X (i + n)) ≫ eqToHom (congrArg Y.X h))

@[reassoc]
private theorem uncurryComponent_ι {X Y Z : CochainComplex C ℤ} (f : Z ⟶ obj X Y)
    (i n k : ℤ) (h : i + n = k) :
    HomologicalComplex.ιTensorObj X Z i n k h ≫ uncurryComponent f k =
      (i * n).negOnePow •
        ((X.X i ◁ f.f n) ≫ (X.X i ◁ Pi.π (family X Y n) i) ≫
          (ihom.ev (X.X i)).app (Y.X (i + n)) ≫ eqToHom (congrArg Y.X h)) := by
  exact GradedObject.Monoidal.ι_tensorObjDesc (X₁ := X.X) (X₂ := Z.X) _ i n h

/-- Uncurry a cochain map out of the explicit internal Hom complex. -/
noncomputable def uncurry {X Y Z : CochainComplex C ℤ} (f : Z ⟶ obj X Y) :
    X ⊗ Z ⟶ Y where
  f k :=
    GradedObject.Monoidal.tensorObjDesc fun i n h ↦
      (i * n).negOnePow •
        ((X.X i ◁ f.f n) ≫
          (X.X i ◁ Pi.π (family X Y n) i) ≫
            (ihom.ev (X.X i)).app (Y.X (i + n)) ≫ eqToHom (congrArg Y.X h))
  comm' := by
    intro k l h
    obtain rfl : k + 1 = l := h
    apply GradedObject.Monoidal.tensorObj_ext
    intro i n h
    subst k
    change HomologicalComplex.ιTensorObj X Z i n (i + n) rfl ≫
      uncurryComponent f (i + n) ≫ Y.d (i + n) (i + n + 1) =
        HomologicalComplex.ιTensorObj X Z i n (i + n) rfl ≫
          (X ⊗ Z).d (i + n) (i + n + 1) ≫ uncurryComponent f (i + n + 1)
    simp only [← Category.assoc]
    rw [uncurryComponent_ι]
    simp only [Category.assoc, eqToHom_refl, Category.comp_id, Linear.units_smul_comp]
    rw [add_assoc i n 1]
    rw [← Category.assoc (HomologicalComplex.ιTensorObj X Z i n _ _), ι_tensor_d]
    simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc,
      uncurryComponent_ι_assoc, uncurryComponent_ι, Linear.comp_units_smul,
      eqToHom_refl, Category.comp_id]
    have hh := congrArg (asCochain X Y) (f.comm n (n + 1))
    simp only [obj, CochainComplex.of_d] at hh
    rw [asCochain_differential] at hh
    have hv := _root_.CochainComplex.HomComplex.Cochain.congr_v hh i (i + (n + 1)) rfl
    rw [_root_.CochainComplex.HomComplex.δ_v _ _ rfl _ _ _ rfl
      (i + n) (i + 1) (by omega) rfl] at hv
    simp only [asCochain, _root_.CochainComplex.HomComplex.Cochain.mk_v,
      Category.assoc, eqToHom_refl, Category.comp_id,
      CategoryTheory.MonoidalClosed.uncurry_natural_left,
      CategoryTheory.MonoidalClosed.uncurry_eq,
      MonoidalCategory.whiskerLeft_comp] at hv
    have hsign : i.negOnePow * (i * (n + 1)).negOnePow = (i * n).negOnePow := by
      rw [← Int.negOnePow_add]
      have ht : i + i * (n + 1) = i * n + 2 * i := by ring
      rw [ht, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]
    rw [smul_smul, hsign]
    have hs := congrArg (fun a ↦ (i * n).negOnePow • a) hv
    rw [← hs]
    simp only [smul_add, smul_smul]
    have hsign' : (i * n).negOnePow * (n + 1).negOnePow =
        -((i + 1) * n).negOnePow := by
      rw [← Int.negOnePow_add,
        show i * n + (n + 1) = (i + 1) * n + 1 by ring, Int.negOnePow_succ]
    rw [hsign', Units.neg_smul]
    change _ = ((i + 1) * n).negOnePow •
      ((X.d i (i + 1) ▷ Z.X n) ≫
        (X.X (i + 1) ◁ f.f n) ≫ (X.X (i + 1) ◁ Pi.π (family X Y n) (i + 1)) ≫
          (ihom.ev (X.X (i + 1))).app (Y.X (i + 1 + n)) ≫ _) +
      (_ + -(((i + 1) * n).negOnePow •
        ((X.d i (i + 1) ▷ Z.X n) ≫
          (X.X (i + 1) ◁ f.f n) ≫ (X.X (i + 1) ◁ Pi.π (family X Y n) (i + 1)) ≫
            (ihom.ev (X.X (i + 1))).app (Y.X (i + 1 + n)) ≫ _)))
    abel

/-- Uncurrying on a homogeneous tensor summand is signed evaluation. -/
@[reassoc (attr := simp)]
theorem ιTensorObj_uncurry_f {X Y Z : CochainComplex C ℤ} (f : Z ⟶ obj X Y)
    (i n k : ℤ) (h : i + n = k) :
    HomologicalComplex.ιTensorObj X Z i n k h ≫ (uncurry f).f k =
      (i * n).negOnePow •
        ((X.X i ◁ f.f n) ≫ (X.X i ◁ Pi.π (family X Y n) i) ≫
          (ihom.ev (X.X i)).app (Y.X (i + n)) ≫ eqToHom (congrArg Y.X h)) := by
  dsimp only [uncurry]
  exact GradedObject.Monoidal.ι_tensorObjDesc (X₁ := X.X) (X₂ := Z.X) _ i n h

/-- Tensor/internal-Hom currying for integer cochain complexes. -/
@[stacks 0FRS "cochain tensor-Hom equivalence"]
noncomputable def homEquiv (X Z Y : CochainComplex C ℤ) :
    (X ⊗ Z ⟶ Y) ≃ (Z ⟶ obj X Y) where
  toFun := curry
  invFun := uncurry
  left_inv f := by
    ext k
    apply GradedObject.Monoidal.tensorObj_ext
    intro i n h
    subst k
    change HomologicalComplex.ιTensorObj X Z i n (i + n) rfl ≫
      (uncurry (curry f)).f (i + n) = _
    rw [ιTensorObj_uncurry_f]
    simp only [eqToHom_refl, Category.comp_id, ← MonoidalCategory.whiskerLeft_comp_assoc,
      curry_f_π]
    change (i * n).negOnePow • CategoryTheory.MonoidalClosed.uncurry
      ((i * n).negOnePow • CategoryTheory.MonoidalClosed.curry
        (HomologicalComplex.ιTensorObj X Z i n (i + n) rfl ≫ f.f (i + n))) = _
    rw [uncurry_units_smul, CategoryTheory.MonoidalClosed.uncurry_curry]
    simp only [smul_smul, Int.units_mul_self, one_smul]
    rfl
  right_inv f := by
    ext n
    apply Pi.hom_ext
    intro i
    rw [curry_f_π, ιTensorObj_uncurry_f]
    simp only [eqToHom_refl, Category.comp_id, curry_units_smul,
      ← MonoidalCategory.whiskerLeft_comp_assoc]
    rw [← CategoryTheory.MonoidalClosed.uncurry_eq,
      CategoryTheory.MonoidalClosed.curry_uncurry]
    simp only [smul_smul, Int.units_mul_self, one_smul]


/-- Naturality data for the cochain tensor/internal-Hom equivalence. -/
noncomputable def coreHomEquiv (X : CochainComplex C ℤ) :
    Adjunction.CoreHomEquiv (tensorLeft X) (functor X) where
  homEquiv Z Y := homEquiv X Z Y
  homEquiv_naturality_left_symm {Z' Z Y} f g := by
    change uncurry (f ≫ g) = HomologicalComplex.tensorHom (𝟙 X) f ≫ uncurry g
    ext k
    apply GradedObject.Monoidal.tensorObj_ext
    intro i n h
    subst k
    change HomologicalComplex.ιTensorObj X Z' i n (i + n) rfl ≫
      (uncurry (f ≫ g)).f (i + n) =
        GradedObject.Monoidal.ιTensorObj X.X Z'.X i n (i + n) rfl ≫
          GradedObject.Monoidal.tensorHom (𝟙 X : X ⟶ X).f f.f (i + n) ≫ (uncurry g).f (i + n)
    simp only [ιTensorObj_uncurry_f, HomologicalComplex.comp_f, Category.assoc,
      MonoidalCategory.whiskerLeft_comp, eqToHom_refl, Category.comp_id]
    simp only [← Category.assoc, GradedObject.Monoidal.ι_tensorHom]
    simp only [HomologicalComplex.id_f, id_tensorHom, Category.assoc,
      ιTensorObj_uncurry_f, Linear.comp_units_smul]
    change _ = (X.X i ◁ f.f n) ≫ HomologicalComplex.ιTensorObj X Z i n (i + n) rfl ≫
      (uncurry g).f (i + n)
    rw [ιTensorObj_uncurry_f]
    simp only [eqToHom_refl, Category.comp_id, Linear.comp_units_smul, Category.assoc]
  homEquiv_naturality_right {Z Y Y'} f g := by
    change curry (f ≫ g) = curry f ≫ map X g
    ext n
    apply Pi.hom_ext
    intro i
    change (curry (f ≫ g)).f n ≫ Pi.π (family X Y' n) i =
      ((curry f).f n ≫ (map X g).f n) ≫ Pi.π (family X Y' n) i
    simp only [curry_f_π, HomologicalComplex.comp_f, Category.assoc,
      CategoryTheory.MonoidalClosed.curry_natural_right, Linear.units_smul_comp,
      map, GradedObject.InternalHom.map, Pi.lift_π_assoc, Pi.lift_π,
      curry_f_π_assoc, Functor.map_comp]

/-- Tensoring by a cochain complex is left adjoint to its internal Hom functor. -/
@[stacks 0FRS "cochain tensor-Hom adjunction"]
noncomputable def adjunction (X : CochainComplex C ℤ) : tensorLeft X ⊣ functor X :=
  Adjunction.mkOfHomEquiv (coreHomEquiv X)

/-- The closed structure represented by the explicit cochain internal Hom. -/
@[implicit_reducible]
noncomputable def closed (X : CochainComplex C ℤ) : Closed X where
  rightAdj := functor X
  adj := adjunction X

/-- The canonical monoidal closed structure on integer cochain complexes. -/
@[stacks 0FRS "closed category of integer cochain complexes", instance_reducible]
noncomputable def monoidalClosed : MonoidalClosed (CochainComplex C ℤ) where
  closed := closed



end CategoryTheory.CochainComplex.InternalHom

end
