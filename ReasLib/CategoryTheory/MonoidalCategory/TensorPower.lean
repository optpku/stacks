/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor powers in a monoidal category

This file owns tensor powers at the representation-independent monoidal-category level. The
construction is functorial in the tensor factor, so concrete categories do not need separate
object and morphism implementations.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped MonoidalCategory

noncomputable section

universe u v u' v'

namespace CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The degree-`n` tensor-power endofunctor with an explicitly chosen degree-zero object. -/
@[stacks 01I8 "tensor-power endofunctor with specified degree zero"]
noncomputable def tensorPowerWithDegreeZeroFunctor (degreeZero : C) : ℕ → C ⥤ C
  | 0 => (Functor.const C).obj degreeZero
  | n + 1 => (𝟭 C).prod' (tensorPowerWithDegreeZeroFunctor degreeZero n) ⋙ tensor C

/-- Iterated left tensor products with `X`, starting from `degreeZero`. -/
@[stacks 01I8 "tensor power with specified degree zero"]
noncomputable abbrev tensorPowerWithDegreeZero
    (degreeZero X : C) (n : ℕ) : C :=
  (tensorPowerWithDegreeZeroFunctor degreeZero n).obj X

/-- The morphism induced on tensor powers with a specified degree-zero object. -/
@[stacks 01I8 "map on tensor powers with specified degree zero"]
noncomputable abbrev tensorPowerWithDegreeZeroMap
    {X Y : C} (degreeZero : C) (f : X ⟶ Y) (n : ℕ) :
    tensorPowerWithDegreeZero degreeZero X n ⟶
      tensorPowerWithDegreeZero degreeZero Y n :=
  (tensorPowerWithDegreeZeroFunctor degreeZero n).map f

/-- The zeroth map with a specified degree-zero object is the identity. -/
@[simp, stacks 01I8 "zeroth map with specified tensor-power degree zero"]
theorem tensorPowerWithDegreeZeroMap_zero
    {X Y : C} (degreeZero : C) (f : X ⟶ Y) :
    tensorPowerWithDegreeZeroMap degreeZero f 0 = 𝟙 _ := rfl

/-- The successor formula for maps with a specified degree-zero object. -/
@[simp, stacks 01I8 "successor map with specified tensor-power degree zero"]
theorem tensorPowerWithDegreeZeroMap_succ
    {X Y : C} (degreeZero : C) (f : X ⟶ Y) (n : ℕ) :
    tensorPowerWithDegreeZeroMap degreeZero f (n + 1) =
      f ⊗ₘ tensorPowerWithDegreeZeroMap degreeZero f n := rfl

/-- An isomorphism of the degree-zero object and tensor factor induces isomorphisms at every
iterated tensor degree. -/
@[stacks 01I8 "isomorphism of tensor powers with specified degree zero"]
noncomputable def tensorPowerWithDegreeZeroMapIso
    {degreeZero degreeZero' X X' : C}
    (e₀ : degreeZero ≅ degreeZero') (e : X ≅ X') :
    (n : ℕ) →
      tensorPowerWithDegreeZero degreeZero X n ≅
        tensorPowerWithDegreeZero degreeZero' X' n
  | 0 => e₀
  | n + 1 => e ⊗ᵢ tensorPowerWithDegreeZeroMapIso e₀ e n

/-- The degree-zero component of the specified-zero tensor-power isomorphism. -/
@[simp, stacks 01I8 "zeroth specified-zero tensor-power isomorphism"]
theorem tensorPowerWithDegreeZeroMapIso_zero
    {degreeZero degreeZero' X X' : C}
    (e₀ : degreeZero ≅ degreeZero') (e : X ≅ X') :
    tensorPowerWithDegreeZeroMapIso e₀ e 0 = e₀ := rfl

/-- The successor component of the specified-zero tensor-power isomorphism. -/
@[simp, stacks 01I8 "successor specified-zero tensor-power isomorphism"]
theorem tensorPowerWithDegreeZeroMapIso_succ
    {degreeZero degreeZero' X X' : C}
    (e₀ : degreeZero ≅ degreeZero') (e : X ≅ X') (n : ℕ) :
    tensorPowerWithDegreeZeroMapIso e₀ e (n + 1) =
      e ⊗ᵢ tensorPowerWithDegreeZeroMapIso e₀ e n := rfl

/-- The zeroth tensor power based at an explicitly chosen object. -/
@[simp, stacks 01I8 "zeroth tensor power with specified degree zero"]
theorem tensorPowerWithDegreeZero_zero (degreeZero X : C) :
    tensorPowerWithDegreeZero degreeZero X 0 = degreeZero := rfl

/-- The successor recursion for tensor powers based at an explicitly chosen object. -/
@[simp, stacks 01I8 "successor tensor power with specified degree zero"]
theorem tensorPowerWithDegreeZero_succ (degreeZero X : C) (n : ℕ) :
    tensorPowerWithDegreeZero degreeZero X (n + 1) =
      tensorObj X (tensorPowerWithDegreeZero degreeZero X n) := rfl

/-- If the chosen degree-zero object is the tensor unit, its iterated powers can be canonically
trivialized back to that object. -/
@[stacks 01I8 "trivialization of specified-zero tensor powers"]
noncomputable def tensorPowerWithDegreeZeroSelfIso
    {U : C} (e : U ≅ 𝟙_ C) :
    (n : ℕ) → tensorPowerWithDegreeZero U U n ≅ U
  | 0 => Iso.refl U
  | n + 1 =>
      eqToIso (Eq.refl _) ≪≫
        (e ⊗ᵢ tensorPowerWithDegreeZeroSelfIso e n) ≪≫ λ_ U

/-- The degree-zero component of the specified-zero tensor-power trivialization. -/
@[simp, stacks 01I8 "zeroth specified-zero tensor-power trivialization"]
theorem tensorPowerWithDegreeZeroSelfIso_zero
    {U : C} (e : U ≅ 𝟙_ C) :
    tensorPowerWithDegreeZeroSelfIso e 0 = Iso.refl U := rfl

/-- The successor component of the specified-zero tensor-power trivialization. -/
@[simp, stacks 01I8 "successor specified-zero tensor-power trivialization"]
theorem tensorPowerWithDegreeZeroSelfIso_succ
    {U : C} (e : U ≅ 𝟙_ C) (n : ℕ) :
    tensorPowerWithDegreeZeroSelfIso e (n + 1) =
      eqToIso (tensorPowerWithDegreeZero_succ U U n) ≪≫
        (e ⊗ᵢ tensorPowerWithDegreeZeroSelfIso e n) ≪≫ λ_ U := rfl

/-- Two tensor powers based at the same chosen degree-zero object canonically concatenate. -/
@[stacks 01I8 "addition of specified-zero tensor powers"]
noncomputable def tensorPowerWithDegreeZeroAddIso
    {degreeZero : C} (e₀ : degreeZero ≅ 𝟙_ C) (X : C) :
    (m n : ℕ) →
      tensorObj (tensorPowerWithDegreeZero degreeZero X m)
          (tensorPowerWithDegreeZero degreeZero X n) ≅
        tensorPowerWithDegreeZero degreeZero X (m + n)
  | 0, n =>
      (e₀ ▷ᵢ tensorPowerWithDegreeZero degreeZero X n) ≪≫
        λ_ (tensorPowerWithDegreeZero degreeZero X n) ≪≫
          eqToIso
            (congrArg (tensorPowerWithDegreeZero degreeZero X) (Nat.zero_add n)).symm
  | m + 1, n =>
      eqToIso
          (congrArg
            (fun K : C ↦ tensorObj K (tensorPowerWithDegreeZero degreeZero X n))
            (Eq.refl _)) ≪≫
        α_ X (tensorPowerWithDegreeZero degreeZero X m)
          (tensorPowerWithDegreeZero degreeZero X n) ≪≫
          (Iso.refl X ⊗ᵢ tensorPowerWithDegreeZeroAddIso e₀ X m n) ≪≫
            eqToIso (Eq.refl _).symm ≪≫
              eqToIso
                (congrArg (tensorPowerWithDegreeZero degreeZero X)
                  (Nat.succ_add m n)).symm

/-- The degree-`n` tensor-power endofunctor on a monoidal category. -/
@[stacks 01I8 "tensor-power endofunctor"]
noncomputable abbrev tensorPowerFunctor (C : Type u) [Category.{v} C] [MonoidalCategory C] :
    ℕ → C ⥤ C :=
  tensorPowerWithDegreeZeroFunctor (𝟙_ C)

/-- The degree-`n` tensor power of an object in a monoidal category. -/
@[stacks 01I8 "tensor power"]
noncomputable abbrev tensorPower (X : C) (n : ℕ) : C :=
  (tensorPowerFunctor C n).obj X

/-- The map on degree-`n` tensor powers induced by a morphism. -/
@[stacks 01I8 "map on tensor powers"]
noncomputable abbrev tensorPowerMap {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    tensorPower X n ⟶ tensorPower Y n :=
  (tensorPowerFunctor C n).map f

/-- The map on zeroth tensor powers is the identity of the monoidal unit. -/
@[simp, stacks 01I8 "zeroth tensor-power map"]
theorem tensorPowerMap_zero {X Y : C} (f : X ⟶ Y) :
    tensorPowerMap f 0 = 𝟙 _ := rfl

/-- Tensor-power maps satisfy the left-recursive successor formula. -/
@[simp, stacks 01I8 "successor tensor-power map"]
theorem tensorPowerMap_succ {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    tensorPowerMap f (n + 1) = f ⊗ₘ tensorPowerMap f n := rfl

/-- An isomorphism of tensor factors induces isomorphisms on all standard tensor powers. -/
@[stacks 01I8 "isomorphism of tensor powers"]
noncomputable abbrev tensorPowerMapIso {X X' : C} (e : X ≅ X') (n : ℕ) :
    tensorPower X n ≅ tensorPower X' n :=
  tensorPowerWithDegreeZeroMapIso (Iso.refl _) e n

/-- Two standard tensor powers canonically concatenate to the tensor power indexed by the sum. -/
@[stacks 01I8 "addition of tensor powers"]
noncomputable abbrev tensorPowerAddIso (X : C) (m n : ℕ) :
    tensorObj (tensorPower X m) (tensorPower X n) ≅ tensorPower X (m + n) :=
  tensorPowerWithDegreeZeroAddIso (Iso.refl _) X m n

/-- The zeroth tensor power is the monoidal unit. -/
@[simp, stacks 01I8 "zeroth tensor power"]
theorem tensorPower_zero (X : C) :
    tensorPower X 0 = 𝟙_ C := rfl

/-- Tensor powers satisfy the left-recursive successor formula. -/
@[simp, stacks 01I8 "successor tensor power"]
theorem tensorPower_succ (X : C) (n : ℕ) :
    tensorPower X (n + 1) = X ⊗ tensorPower X n := rfl

end CategoryTheory.MonoidalCategory

namespace CategoryTheory.Functor.Monoidal

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
variable [MonoidalCategory C] [MonoidalCategory D]
variable (F : C ⥤ D) [F.Monoidal]

/-- The canonical tensor-power comparison of a monoidal functor.  It is recursively built from
the unit isomorphism and tensorator, so it is available independently of any concrete category. -/
@[stacks 01I8 "monoidal functor tensor-power comparison"]
noncomputable def tensorPowerIso (X : C) :
    (n : ℕ) →
      tensorPower (F.obj X) n ≅ F.obj (tensorPower X n)
  | 0 => Functor.Monoidal.εIso F
  | n + 1 =>
      (Iso.refl (F.obj X) ⊗ᵢ tensorPowerIso X n) ≪≫
        Functor.Monoidal.μIso F X (tensorPower X n)

/-- In degree zero, a monoidal functor's tensor-power comparison is its unit isomorphism. -/
@[simp, stacks 01I8 "monoidal functor tensor-power comparison in degree zero"]
theorem tensorPowerIso_zero (X : C) :
    tensorPowerIso F X 0 = Functor.Monoidal.εIso F := rfl

/-- In successor degree, a monoidal functor's tensor-power comparison tensors the preceding one
and then applies the tensorator. -/
@[simp, stacks 01I8 "monoidal functor tensor-power comparison in successor degree"]
theorem tensorPowerIso_succ (X : C) (n : ℕ) :
    tensorPowerIso F X (n + 1) =
      (Iso.refl (F.obj X) ⊗ᵢ tensorPowerIso F X n) ≪≫
        Functor.Monoidal.μIso F X (tensorPower X n) := rfl

/-- The monoidal-functor tensor-power comparison is natural in its source object. -/
@[stacks 01I8 "naturality of monoidal functor tensor-power comparison"]
theorem tensorPowerIso_naturality {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    tensorPowerMap (F.map f) n ≫ (tensorPowerIso F Y n).hom =
      (tensorPowerIso F X n).hom ≫
        F.map (tensorPowerMap f n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [tensorPowerMap_succ, tensorPowerIso_succ, Iso.trans_hom,
      tensorIso_hom, Iso.refl_hom, μIso_hom]
    calc
      (F.map f ⊗ₘ tensorPowerMap (F.map f) n) ≫
          (𝟙 (F.obj Y) ⊗ₘ (tensorPowerIso F Y n).hom) ≫
          LaxMonoidal.μ F Y (tensorPower Y n) =
        (F.map f ⊗ₘ (tensorPowerMap (F.map f) n ≫
          (tensorPowerIso F Y n).hom)) ≫
          LaxMonoidal.μ F Y (tensorPower Y n) := by
            rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]
      _ = (F.map f ⊗ₘ ((tensorPowerIso F X n).hom ≫
          F.map (tensorPowerMap f n))) ≫
          LaxMonoidal.μ F Y (tensorPower Y n) := by rw [ih]
      _ = (𝟙 (F.obj X) ⊗ₘ (tensorPowerIso F X n).hom) ≫
          (F.map f ⊗ₘ F.map (tensorPowerMap f n)) ≫
          LaxMonoidal.μ F Y (tensorPower Y n) := by
            rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
      _ = _ := by
        rw [LaxMonoidal.μ_natural, ← Category.assoc]
        rfl

/-- The inverse monoidal-functor tensor-power comparison is natural in its source object. -/
@[stacks 01I8 "naturality of inverse monoidal functor tensor-power comparison"]
theorem tensorPowerIso_inv_naturality {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    F.map (tensorPowerMap f n) ≫ (tensorPowerIso F Y n).inv =
      (tensorPowerIso F X n).inv ≫ tensorPowerMap (F.map f) n := by
  apply (cancel_epi (tensorPowerIso F X n).hom).1
  simpa [Category.assoc] using
    congrArg (fun k => k ≫ (tensorPowerIso F Y n).inv)
      (tensorPowerIso_naturality F f n).symm

/-- The pointwise tensor-power comparisons assemble into a natural isomorphism of functors. -/
@[stacks 01I8 "monoidal functor tensor-power natural isomorphism"]
noncomputable def tensorPowerNatIso (n : ℕ) :
    F ⋙ tensorPowerFunctor D n ≅ tensorPowerFunctor C n ⋙ F :=
  NatIso.ofComponents
    (fun X ↦ tensorPowerIso F X n)
    (fun f ↦ tensorPowerIso_naturality F f n)

end CategoryTheory.Functor.Monoidal


