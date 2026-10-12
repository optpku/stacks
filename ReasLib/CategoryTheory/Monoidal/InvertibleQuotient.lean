/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Category
public import ReasLib.CategoryTheory.Monoidal.Invertible

/-!
# Invertible quotients in monoidal categories

This file owns the category-independent data of an epimorphism onto an invertible
object of a monoidal category. Geometric projective-bundle constructions specialize
this owner to categories of module sheaves.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- An epimorphic quotient whose target is invertible for the monoidal product. -/
@[stacks 0FFN "invertible quotient in a monoidal category"]
structure InvertibleQuotient (E : C) where
  /-- The target of the quotient. -/
  object : C
  /-- The target is invertible for the canonical monoidal object property. -/
  isInvertible : MonoidalCategory.isInvertibleObject object
  /-- The quotient morphism. -/
  hom : E ⟶ object
  /-- The quotient morphism is an epimorphism. -/
  hom_epi : Epi hom

namespace InvertibleQuotient

/-- Precomposing an invertible quotient with an isomorphism of its source gives an invertible
quotient of the isomorphic source. -/
@[stacks 0FFN "source transport of an invertible quotient"]
def precomposeIso {E E' : C} (e : E ≅ E') (q : InvertibleQuotient E') :
    InvertibleQuotient E where
  object := q.object
  isInvertible := q.isInvertible
  hom := e.hom ≫ q.hom
  hom_epi := epi_comp' (inferInstance : Epi e.hom) q.hom_epi

/-- Transporting an invertible quotient along an isomorphism and its inverse recovers the
original quotient. -/
@[stacks 0FFN "inverse source transport of an invertible quotient"]
theorem precomposeIso_symm_apply {E E' : C} (e : E ≅ E')
    (q : InvertibleQuotient E') :
    precomposeIso e.symm (precomposeIso e q) = q := by
  cases q
  simp [precomposeIso]

/-- Isomorphic source objects have equivalent types of invertible quotients. -/
@[stacks 0FFN "invertible-quotient equivalence under source isomorphism"]
def equivOfIso {E E' : C} (e : E ≅ E') :
    InvertibleQuotient E ≃ InvertibleQuotient E' where
  toFun := precomposeIso e.symm
  invFun := precomposeIso e
  left_inv := precomposeIso_symm_apply e.symm
  right_inv := precomposeIso_symm_apply e

/-- The target object is unchanged by precomposing an invertible quotient with a source
isomorphism. -/
@[simp, stacks 0FFN "source transport preserves the quotient target"]
theorem precomposeIso_object {E E' : C} (e : E ≅ E') (q : InvertibleQuotient E') :
    (precomposeIso e q).object = q.object := rfl

/-- The quotient morphism after source-isomorphism transport is the stated composite. -/
@[simp, stacks 0FFN "source transport quotient morphism"]
theorem precomposeIso_hom {E E' : C} (e : E ≅ E') (q : InvertibleQuotient E') :
    (precomposeIso e q).hom = e.hom ≫ q.hom := rfl

end InvertibleQuotient

end CategoryTheory
