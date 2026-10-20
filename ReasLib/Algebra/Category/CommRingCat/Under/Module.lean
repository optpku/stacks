module

public import Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
# The underlying module of a commutative algebra under a ring

@stack 08NA

An object of `Under A` is canonically a commutative `A`-algebra, hence in particular an
`A`-module.  This file owns that forgetful functor independently of any resolution built from it.
-/

@[expose] public section

open CategoryTheory

universe u

namespace CommRingCat.Under

variable (A : CommRingCat.{u})

/-- The forgetful functor from commutative rings under `A` to `A`-modules. -/
@[stacks 08NA "underlying module of a commutative algebra under a ring"]
abbrev forgetToModule : Under A ⥤ ModuleCat A :=
  (commAlgCatEquivUnder A).inverse ⋙
    forget₂ (CommAlgCat A) (AlgCat A) ⋙ forget₂ (AlgCat A) (ModuleCat A)

/-- On objects, `forgetToModule` equips the underlying ring with its canonical `A`-module
structure. -/
@[simp, stacks 08NA "underlying module functor on objects"]
theorem forgetToModule_obj (B : Under A) :
    (forgetToModule A).obj B = ModuleCat.of A B := sorry

/-- On morphisms, `forgetToModule` is the linear map underlying the canonical `A`-algebra map. -/
@[simp, stacks 08NA "underlying module functor on morphisms"]
theorem forgetToModule_map {B C : Under A} (f : B ⟶ C) :
    (forgetToModule A).map f =
      ModuleCat.ofHom (CommRingCat.toAlgHom f).toLinearMap := sorry

/-- Forgetting an `A`-algebra first to an `A`-module and then to its carrier agrees with
forgetting its underlying commutative ring directly to its carrier. -/
@[simp, stacks 08NA "compatibility of the underlying module and carrier functors"]
theorem forgetToModule_comp_forget :
    forgetToModule A ⋙ CategoryTheory.forget (ModuleCat A) =
      Under.forget A ⋙ CategoryTheory.forget CommRingCat := sorry

end CommRingCat.Under
