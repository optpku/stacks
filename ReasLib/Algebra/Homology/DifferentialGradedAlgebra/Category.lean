module

public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra

/-!
# The category of chain differential graded algebras

This file supplies the categorical laws for the concrete chain-DGA
homomorphisms defined in `DifferentialGradedAlgebra.Basic` and installs their
canonical category instance.
-/

@[expose] public section

universe u v

open CategoryTheory

variable {R : Type u} [CommRing R]

namespace ChainDGAlgebra.Hom

variable {A B C D : ChainDGAlgebra.{u, v} R}

/-- Composing a chain-DGA homomorphism with the identity of its source is neutral. -/
@[simp]
theorem id_comp (f : Hom A B) : comp f (id A) = f := sorry

/-- Composing the identity of the target with a chain-DGA homomorphism is neutral. -/
@[simp]
theorem comp_id (f : Hom A B) : comp (id B) f = f := sorry

/-- Composition of chain-DGA homomorphisms is associative. -/
theorem comp_assoc (f : Hom A B) (g : Hom B C) (h : Hom C D) :
    comp h (comp g f) = comp (comp h g) f := sorry

end ChainDGAlgebra.Hom

namespace ChainDGAlgebra

/-- Chain differential graded algebras form a category. -/
@[stacks 09PR "infrastructure: the category of chain differential graded algebras"]
instance instCategory : Category (ChainDGAlgebra.{u, v} R) where
  Hom A B := Hom A B
  id A := Hom.id A
  comp f g := Hom.comp g f
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.comp_assoc

/-- A categorical chain-DGA arrow acts degreewise on homogeneous elements. -/
instance instCategoryCoeFun {A B : ChainDGAlgebra.{u, v} R} :
    CoeFun (A ⟶ B) (fun _ ↦ ∀ i : ℤ, A.X i → B.X i) where
  coe f := fun i x ↦ ((f : Hom A B).toChainMap.f i) x

/-- The categorical identity is the explicit identity chain-DGA homomorphism. -/
@[simp]
theorem category_id (A : ChainDGAlgebra.{u, v} R) :
    (𝟙 A : A ⟶ A) = (Hom.id A : A ⟶ A) := sorry

/-- Categorical composition is explicit composition of chain-DGA homomorphisms. -/
@[simp]
theorem category_comp {A B C : ChainDGAlgebra.{u, v} R} (f : A ⟶ B) (g : B ⟶ C) :
    f ≫ g = (Hom.comp (g : Hom B C) (f : Hom A B) : A ⟶ C) := sorry

end ChainDGAlgebra
