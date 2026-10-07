module

public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Preadditive dependent product categories

The dependent product of preadditive categories is preadditive pointwise.  Evaluation and the
standard functors assembled from indexed families are additive.  Registering these facts globally
lets constructions valued in a family of module categories act on homological complexes without
rebuilding zero-morphism instances locally.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u v' u' uA vA

namespace CategoryTheory.Pi

variable {I : Type w}
variable (C : I → Type u) [∀ i, Category.{v} (C i)] [∀ i, Preadditive (C i)]

/-- The dependent product of preadditive categories is preadditive pointwise. -/
@[stacks 0FKS "preadditive structure on a dependent product category"]
noncomputable instance preadditive : Preadditive (∀ i, C i) where
  homGroup := fun X Y ↦
    inferInstanceAs (AddCommGroup (∀ i, X i ⟶ Y i))
  add_comp := sorry
  comp_add := sorry

/-- Evaluation at one coordinate of a dependent product category is additive. -/
instance eval_additive (i : I) : (CategoryTheory.Pi.eval C i).Additive := sorry

end CategoryTheory.Pi

namespace CategoryTheory.Functor

variable {I : Type w}
variable {C : I → Type u} [∀ i, Category.{v} (C i)] [∀ i, Preadditive (C i)]
variable {D : I → Type u'} [∀ i, Category.{v'} (D i)] [∀ i, Preadditive (D i)]

/-- A pointwise family of additive functors induces an additive functor between dependent product
categories. -/
instance pi_additive (F : ∀ i, C i ⥤ D i) [∀ i, (F i).Additive] :
    (Functor.pi F).Additive := sorry

/-- A family of additive functors with common source induces an additive functor to the dependent
product category. -/
instance pi'_additive
    {A : Type uA} [Category.{vA} A] [Preadditive A]
    (F : ∀ i, A ⥤ C i) [∀ i, (F i).Additive] :
    (Functor.pi' F).Additive := sorry

end CategoryTheory.Functor

end
