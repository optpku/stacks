/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Monoid objects from homogeneous multiplication maps

For a naturally graded object, a degree-zero unit and multiplication maps between every pair of
homogeneous components assemble canonically into morphisms from Mathlib's graded tensor product.
This leaf owns that coproduct assembly independently of any particular algebra construction.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonObj

noncomputable section

universe u v w

namespace CategoryTheory.GradedObject.Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section Unit

variable {I : Type w} [AddMonoid I] [DecidableEq I] [HasInitial C]

/-- Assemble a degree-zero unit into a morphism from the tensor unit of naturally graded
objects. -/
@[stacks 0FQW "degree-zero unit of a graded monoid object"]
noncomputable def oneHom (A : GradedObject I C) (one : 𝟙_ C ⟶ A 0) :
    (tensorUnit : GradedObject I C) ⟶ A :=
  fun n ↦ if h : n = 0 then
    (singleObjApplyIsoOfEq 0 (𝟙_ C) n h).hom ≫
      one ≫ eqToHom (congrArg A h).symm
  else
    (isInitialTensorUnitApply n h).to (A n)

/-- The degree-zero component of the assembled graded unit is the supplied unit map. -/
@[simp]
theorem oneHom_zero (A : GradedObject I C) (one : 𝟙_ C ⟶ A 0) :
    oneHom A one 0 = tensorUnit₀.hom ≫ one := sorry

/-- Away from degree zero, the assembled graded unit is the unique map from the initial
component of the graded tensor unit. -/
theorem oneHom_of_ne_zero (A : GradedObject I C) (one : 𝟙_ C ⟶ A 0)
    (n : I) (h : n ≠ 0) :
    oneHom A one n = (isInitialTensorUnitApply n h).to (A n) := sorry

/-- A morphism of graded objects commutes with assembled units as soon as its degree-zero
component preserves the supplied unit. -/
theorem oneHom_naturality {A B : GradedObject I C}
    (oneA : 𝟙_ C ⟶ A 0) (oneB : 𝟙_ C ⟶ B 0) (f : A ⟶ B)
    (h : oneA ≫ f 0 = oneB) :
    oneHom A oneA ≫ f = oneHom B oneB := sorry

end Unit

section Multiplication

variable {I : Type w} [AddMonoid I]

/-- Assemble homogeneous multiplication maps into a morphism from the graded tensor square. -/
@[stacks 0FQW "multiplication of a graded monoid object"]
noncomputable def mulHom (A : GradedObject I C) [HasTensor A A]
    (mul : ∀ i j : I, A i ⊗ A j ⟶ A (i + j)) : tensorObj A A ⟶ A :=
  fun _ ↦ tensorObjDesc (X₁ := A) (X₂ := A) fun i j h ↦
    mul i j ≫ eqToHom (congrArg A h)

/-- Restricting the assembled graded multiplication to a homogeneous summand recovers the
supplied fixed-degree multiplication, followed by the requested degree identification. -/
@[reassoc]
theorem ι_mulHom (A : GradedObject I C) [HasTensor A A]
    (mul : ∀ i j : I, A i ⊗ A j ⟶ A (i + j))
    (i j n : I) (h : i + j = n) :
    ιTensorObj A A i j n h ≫ mulHom A mul n =
      mul i j ≫ eqToHom (congrArg A h) := sorry

/-- On the summand indexed by `(i, j)`, assembled multiplication is exactly the supplied
homogeneous multiplication map. -/
@[reassoc (attr := simp)]
theorem ι_mulHom_add (A : GradedObject I C) [HasTensor A A]
    (mul : ∀ i j : I, A i ⊗ A j ⟶ A (i + j)) (i j : I) :
    ιTensorObj A A i j (i + j) rfl ≫ mulHom A mul (i + j) = mul i j := sorry

/-- A morphism of graded objects commutes with assembled multiplication as soon as it preserves
every homogeneous multiplication map. -/
theorem mulHom_naturality {A B : GradedObject I C} [HasTensor A A] [HasTensor B B]
    (mulA : ∀ i j : I, A i ⊗ A j ⟶ A (i + j))
    (mulB : ∀ i j : I, B i ⊗ B j ⟶ B (i + j)) (f : A ⟶ B)
    (h : ∀ i j : I, mulA i j ≫ f (i + j) =
      (f i ⊗ₘ f j) ≫ mulB i j) :
    mulHom A mulA ≫ f = tensorHom f f ≫ mulHom B mulB := sorry

end Multiplication

section Action

variable {I : Type w} [AddMonoid I]

/-- Assemble homogeneous right-action maps into a morphism from the graded tensor product. -/
noncomputable def actionHom (M A : GradedObject I C) [HasTensor M A]
    (act : ∀ i j : I, M i ⊗ A j ⟶ M (i + j)) : tensorObj M A ⟶ M :=
  fun _ ↦ tensorObjDesc (X₁ := M) (X₂ := A) fun i j h ↦
    act i j ≫ eqToHom (congrArg M h)

/-- Restricting an assembled graded action to a homogeneous summand recovers the supplied
fixed-degree action, followed by the requested degree identification. -/
@[reassoc]
theorem ι_actionHom (M A : GradedObject I C) [HasTensor M A]
    (act : ∀ i j : I, M i ⊗ A j ⟶ M (i + j))
    (i j n : I) (h : i + j = n) :
    ιTensorObj M A i j n h ≫ actionHom M A act n =
      act i j ≫ eqToHom (congrArg M h) := sorry

/-- On the summand indexed by `(i, j)`, an assembled graded action is exactly the supplied
homogeneous action map. -/
@[reassoc (attr := simp)]
theorem ι_actionHom_add (M A : GradedObject I C) [HasTensor M A]
    (act : ∀ i j : I, M i ⊗ A j ⟶ M (i + j)) (i j : I) :
    ιTensorObj M A i j (i + j) rfl ≫ actionHom M A act (i + j) = act i j := sorry

/-- Morphisms of graded objects commute with assembled actions when they preserve every
homogeneous action map. -/
theorem actionHom_naturality {M N A B : GradedObject I C}
    [HasTensor M A] [HasTensor N B]
    (actM : ∀ i j : I, M i ⊗ A j ⟶ M (i + j))
    (actN : ∀ i j : I, N i ⊗ B j ⟶ N (i + j))
    (f : M ⟶ N) (g : A ⟶ B)
    (h : ∀ i j : I, actM i j ≫ f (i + j) =
      (f i ⊗ₘ g j) ≫ actN i j) :
    actionHom M A actM ≫ f = tensorHom f g ≫ actionHom N B actN := sorry

end Action

section NatMonoid

variable [HasFiniteCoproducts C]
variable [∀ X : C, PreservesFiniteCoproducts ((curriedTensor C).obj X)]
variable [∀ X : C, PreservesFiniteCoproducts ((curriedTensor C).flip.obj X)]

/-- Assemble homogeneous unit and multiplication maps, together with their categorical laws,
into Mathlib's monoid-object structure on a naturally graded object. -/
@[stacks 0FQW "naturally graded monoid-object constructor", implicit_reducible]
noncomputable def monObj (A : GradedObject ℕ C) (one : 𝟙_ C ⟶ A 0)
    (mul : ∀ i j : ℕ, A i ⊗ A j ⟶ A (i + j))
    (one_mul : oneHom A one ▷ A ≫ mulHom A mul = (λ_ A).hom)
    (mul_one : A ◁ oneHom A one ≫ mulHom A mul = (ρ_ A).hom)
    (mul_assoc : (mulHom A mul ▷ A) ≫ mulHom A mul =
      (α_ A A A).hom ≫ (A ◁ mulHom A mul) ≫ mulHom A mul) : MonObj A where
  one := oneHom A one
  mul := mulHom A mul
  one_mul := one_mul
  mul_one := mul_one
  mul_assoc := mul_assoc

/-- Bundle a naturally graded object with assembled homogeneous multiplication as an object of
`Mon (GradedObject ℕ C)`. -/
@[stacks 0FQW "bundled naturally graded monoid", implicit_reducible]
noncomputable def mon (A : GradedObject ℕ C) (one : 𝟙_ C ⟶ A 0)
    (mul : ∀ i j : ℕ, A i ⊗ A j ⟶ A (i + j))
    (one_mul : oneHom A one ▷ A ≫ mulHom A mul = (λ_ A).hom)
    (mul_one : A ◁ oneHom A one ≫ mulHom A mul = (ρ_ A).hom)
    (mul_assoc : (mulHom A mul ▷ A) ≫ mulHom A mul =
      (α_ A A A).hom ≫ (A ◁ mulHom A mul) ≫ mulHom A mul) :
    Mon (GradedObject ℕ C) where
  X := A
  mon := monObj A one mul one_mul mul_one mul_assoc

/-- The underlying object of a graded monoid assembled from homogeneous components is the
original graded object. -/
@[simp]
theorem mon_X (A : GradedObject ℕ C) (one : 𝟙_ C ⟶ A 0)
    (mul : ∀ i j : ℕ, A i ⊗ A j ⟶ A (i + j))
    (one_mul : oneHom A one ▷ A ≫ mulHom A mul = (λ_ A).hom)
    (mul_one : A ◁ oneHom A one ≫ mulHom A mul = (ρ_ A).hom)
    (mul_assoc : (mulHom A mul ▷ A) ≫ mulHom A mul =
      (α_ A A A).hom ≫ (A ◁ mulHom A mul) ≫ mulHom A mul) :
    (mon A one mul one_mul mul_one mul_assoc).X = A := sorry

/-- The unit of the bundled graded monoid is the unit assembled from degree zero. -/
@[simp]
theorem mon_one (A : GradedObject ℕ C) (one : 𝟙_ C ⟶ A 0)
    (mul : ∀ i j : ℕ, A i ⊗ A j ⟶ A (i + j))
    (one_mul : oneHom A one ▷ A ≫ mulHom A mul = (λ_ A).hom)
    (mul_one : A ◁ oneHom A one ≫ mulHom A mul = (ρ_ A).hom)
    (mul_assoc : (mulHom A mul ▷ A) ≫ mulHom A mul =
      (α_ A A A).hom ≫ (A ◁ mulHom A mul) ≫ mulHom A mul) :
    η[(mon A one mul one_mul mul_one mul_assoc).X] = oneHom A one := sorry

/-- The multiplication of the bundled graded monoid is the multiplication assembled from its
homogeneous components. -/
@[simp]
theorem mon_mul (A : GradedObject ℕ C) (one : 𝟙_ C ⟶ A 0)
    (mul : ∀ i j : ℕ, A i ⊗ A j ⟶ A (i + j))
    (one_mul : oneHom A one ▷ A ≫ mulHom A mul = (λ_ A).hom)
    (mul_one : A ◁ oneHom A one ≫ mulHom A mul = (ρ_ A).hom)
    (mul_assoc : (mulHom A mul ▷ A) ≫ mulHom A mul =
      (α_ A A A).hom ≫ (A ◁ mulHom A mul) ≫ mulHom A mul) :
    μ[(mon A one mul one_mul mul_one mul_assoc).X] = mulHom A mul := sorry

/-- Restricting bundled graded multiplication to the summand of degrees `(i, j)` recovers the
supplied homogeneous multiplication. -/
@[reassoc (attr := simp)]
theorem ι_mon_mul_add (A : GradedObject ℕ C) (one : 𝟙_ C ⟶ A 0)
    (mul : ∀ i j : ℕ, A i ⊗ A j ⟶ A (i + j))
    (one_mul : oneHom A one ▷ A ≫ mulHom A mul = (λ_ A).hom)
    (mul_one : A ◁ oneHom A one ≫ mulHom A mul = (ρ_ A).hom)
    (mul_assoc : (mulHom A mul ▷ A) ≫ mulHom A mul =
      (α_ A A A).hom ≫ (A ◁ mulHom A mul) ≫ mulHom A mul)
    (i j : ℕ) :
    ιTensorObj A A i j (i + j) rfl ≫
      μ[(mon A one mul one_mul mul_one mul_assoc).X] (i + j) = mul i j := sorry

end NatMonoid

end CategoryTheory.GradedObject.Monoidal
