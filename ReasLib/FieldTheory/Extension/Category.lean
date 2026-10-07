module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.EssentialFiniteness

/-!
# Finitely generated field extensions

This file packages finitely generated field extensions of a fixed field as a
full subcategory of commutative algebras.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FinitelyGeneratedFieldExtension

/-- The property that a commutative `k`-algebra is a field finitely generated over `k`. -/
def property (k : Type u) [Field k] : ObjectProperty (CommAlgCat.{u} k) :=
  fun K ↦ IsField K ∧ Algebra.EssFiniteType k K

/-- The category of finitely generated field extensions of `k` and `k`-algebra maps. -/
abbrev Cat (k : Type u) [Field k] :=
  (property k).FullSubcategory

end AlgebraicGeometry.FinitelyGeneratedFieldExtension
