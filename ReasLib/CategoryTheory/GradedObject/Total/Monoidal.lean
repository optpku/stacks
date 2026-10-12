/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.GradedObject.Braiding
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import ReasLib.CategoryTheory.GradedObject.Total.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# The total functor as a monoidal functor

The coproduct of the homogeneous pieces of a naturally graded object is its total object.  This
file records the canonical unit and tensor comparison isomorphisms explicitly, then equips the
total functor with the corresponding monoidal and braided structures.  Consequently Mathlib's
`Functor.mapMon` and `Functor.mapCommMon` apply directly to graded monoid objects.
-/

@[expose] public section

open CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe w v u

namespace CategoryTheory.GradedObject.Total

section Unit

variable {I : Type w} [AddMonoid I] [DecidableEq I]
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [HasInitial C] [HasCoproductsOfShape I C]

/-- The tensor unit maps to the total object of the graded tensor unit through its degree-zero
summand. -/
noncomputable def unitHom :
    𝟙_ C ⟶ ∐ fun i : I ↦ (Monoidal.tensorUnit : GradedObject I C) i :=
  Monoidal.tensorUnit₀.inv ≫ Sigma.ι _ 0

/-- Collapse the total object of the graded tensor unit onto its unique noninitial summand. -/
noncomputable def unitInv :
    (∐ fun i : I ↦ (Monoidal.tensorUnit : GradedObject I C) i) ⟶ 𝟙_ C :=
  Sigma.desc fun i ↦
    if h : i = 0 then
      (singleObjApplyIsoOfEq 0 (𝟙_ C) i h).hom
    else
      (Monoidal.isInitialTensorUnitApply i h).to (𝟙_ C)

/-- The total object of the graded tensor unit is canonically the tensor unit. -/
@[stacks 01CF "total functor unit isomorphism"]
noncomputable def unitIso :
    𝟙_ C ≅ (functor (I := I) (C := C)).obj
      (Monoidal.tensorUnit : GradedObject I C) where
  hom := unitHom
  inv := unitInv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward unit comparison is the inclusion of degree zero. -/
theorem unitIso_hom :
    (unitIso (I := I) (C := C)).hom =
      Monoidal.tensorUnit₀.inv ≫ Sigma.ι _ 0 := sorry

end Unit

section Tensor

variable {I : Type w} [AddMonoid I]
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [HasCoproductsOfShape I C]
variable [∀ Z : C, PreservesColimitsOfShape (Discrete I) ((curriedTensor C).obj Z)]
variable [∀ Z : C, PreservesColimitsOfShape (Discrete I) ((curriedTensor C).flip.obj Z)]

/-- Distribute the tensor product of two total objects over both coproducts and include each
homogeneous product into its total degree. -/
noncomputable def tensorHom (X Y : GradedObject I C) [HasTensor X Y] :
    ((functor (I := I) (C := C)).obj X ⊗
        (functor (I := I) (C := C)).obj Y) ⟶
      (functor (I := I) (C := C)).obj (Monoidal.tensorObj X Y) :=
  (PreservesCoproduct.iso ((curriedTensor C).flip.obj (∐ Y)) X).hom ≫
    Limits.Sigma.map (fun i ↦
      (PreservesCoproduct.iso ((curriedTensor C).obj (X i)) Y).hom) ≫
    Sigma.desc fun i ↦
      Sigma.desc fun j ↦
        Monoidal.ιTensorObj X Y i j (i + j) rfl ≫ Sigma.ι _ (i + j)

/-- Project a total graded tensor product to homogeneous pairs and include both entries in their
respective total objects. -/
noncomputable def tensorInv (X Y : GradedObject I C) [HasTensor X Y] :
    (functor (I := I) (C := C)).obj (Monoidal.tensorObj X Y) ⟶
      (functor (I := I) (C := C)).obj X ⊗
        (functor (I := I) (C := C)).obj Y :=
  Sigma.desc fun _ ↦
    Monoidal.tensorObjDesc fun i j _ ↦ Sigma.ι X i ⊗ₘ Sigma.ι Y j

/-- Totalization carries the graded tensor product to the tensor product of total objects. -/
@[stacks 01CF "total functor tensor isomorphism"]
noncomputable def tensorIso (X Y : GradedObject I C) [HasTensor X Y] :
    (functor (I := I) (C := C)).obj X ⊗
        (functor (I := I) (C := C)).obj Y ≅
      (functor (I := I) (C := C)).obj (Monoidal.tensorObj X Y) where
  hom := tensorHom X Y
  inv := tensorInv X Y
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- On a pair of homogeneous summands, the forward tensor comparison is inclusion into total
degree `i + j`. -/
@[reassoc]
theorem ι_tensorIso_hom (X Y : GradedObject I C) [HasTensor X Y] (i j : I) :
    (Sigma.ι X i ⊗ₘ Sigma.ι Y j) ≫ (tensorIso X Y).hom =
      Monoidal.ιTensorObj X Y i j (i + j) rfl ≫ Sigma.ι _ (i + j) := sorry

/-- The inverse tensor comparison sends every homogeneous tensor summand to the tensor of the
two coproduct inclusions. -/
@[reassoc]
theorem ι_tensorIso_inv (X Y : GradedObject I C) [HasTensor X Y]
    (i j n : I) (h : i + j = n) :
    Monoidal.ιTensorObj X Y i j n h ≫ Sigma.ι _ n ≫ (tensorIso X Y).inv =
      Sigma.ι X i ⊗ₘ Sigma.ι Y j := sorry

end Tensor

section NatMonoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [HasFiniteCoproducts C]
variable [∀ Z : C, PreservesFiniteCoproducts ((curriedTensor C).obj Z)]
variable [∀ Z : C, PreservesFiniteCoproducts ((curriedTensor C).flip.obj Z)]
variable [HasCoproductsOfShape ℕ C]
variable [∀ Z : C, PreservesColimitsOfShape (Discrete ℕ) ((curriedTensor C).obj Z)]
variable [∀ Z : C, PreservesColimitsOfShape (Discrete ℕ) ((curriedTensor C).flip.obj Z)]

/-- The canonical coherence data making totalization of naturally graded objects monoidal. -/
@[stacks 01CF "total functor monoidal structure"]
noncomputable def coreMonoidal :
    (functor (I := ℕ) (C := C)).CoreMonoidal where
  εIso := unitIso (I := ℕ) (C := C)
  μIso := fun X Y ↦ tensorIso X Y
  μIso_hom_natural_left := sorry
  μIso_hom_natural_right := sorry
  associativity := sorry
  left_unitality := sorry
  right_unitality := sorry

/-- Totalization of naturally graded objects is a monoidal functor. -/
@[stacks 01CF "total functor is monoidal", implicit_reducible]
noncomputable instance monoidal :
    (functor (I := ℕ) (C := C)).Monoidal :=
  coreMonoidal.toMonoidal

/-- Mapping graded monoids through totalization and then forgetting multiplication is the same as
forgetting first and totalizing the underlying graded object. -/
@[stacks 01CF "underlying object of a total graded monoid"]
theorem mapMon_comp_forget :
    (functor (I := ℕ) (C := C)).mapMon ⋙ Mon.forget C =
      Mon.forget (GradedObject ℕ C) ⋙ functor (I := ℕ) (C := C) := sorry

end NatMonoidal

section NatBraided

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
variable [HasFiniteCoproducts C]
variable [∀ Z : C, PreservesFiniteCoproducts ((curriedTensor C).obj Z)]
variable [∀ Z : C, PreservesFiniteCoproducts ((curriedTensor C).flip.obj Z)]
variable [HasCoproductsOfShape ℕ C]
variable [∀ Z : C, PreservesColimitsOfShape (Discrete ℕ) ((curriedTensor C).obj Z)]
variable [∀ Z : C, PreservesColimitsOfShape (Discrete ℕ) ((curriedTensor C).flip.obj Z)]

/-- For the unsigned braiding, totalization preserves the braiding and hence transports
commutative graded monoid objects to commutative monoid objects. -/
@[stacks 01CF "total functor preserves the unsigned braiding", implicit_reducible]
noncomputable instance braided :
    (functor (I := ℕ) (C := C)).Braided where
  braided := sorry

/-- Mapping graded commutative monoids through totalization and forgetting is totalization of the
underlying graded object. -/
@[stacks 01CF "underlying object of a total graded commutative monoid"]
theorem mapCommMon_comp_forget :
    (functor (I := ℕ) (C := C)).mapCommMon ⋙ CommMon.forget C =
      CommMon.forget (GradedObject ℕ C) ⋙ functor (I := ℕ) (C := C) := sorry

end NatBraided

end CategoryTheory.GradedObject.Total
