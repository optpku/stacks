module

public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
public import Mathlib.CategoryTheory.Category.Cat
public import ReasLib.CategoryTheory.Cofibered.Fiber
public import ReasLib.CategoryTheory.Cofibered.InGroupoids

/-!
# Pseudofunctoriality of chosen pushforwards

Chosen pushforwards extend the standard groupoid fibres and their covariant fibre functors
to a pseudofunctor on the base category.
-/

@[expose] public section

universe u v uF vF

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {F : Type uF} [Category.{vF} F]

/-- A cleavage of the opposite of a cofibered-in-groupoids projection supplies coherent
pseudofunctoriality for its standard fibres and the prescribed pushforward functors. -/
theorem Functor.existsPushforwardPseudofunctor (p : F ⥤ C) [IsFibered.InGroupoids p.op]
    (χ : p.op.Cleavage) :
    ∃ P : LocallyDiscrete C ⥤ᵖ Cat.{vF, uF},
      (∀ U : C, P.obj (LocallyDiscrete.mk U) = Cat.of (p.Fiber U)) ∧
      (∀ {U V : C} (f : U ⟶ V),
        HEq (P.map f.toLoc) (Functor.pushforwardFiberFunctor p χ f).toCatHom) := sorry

end CategoryTheory
