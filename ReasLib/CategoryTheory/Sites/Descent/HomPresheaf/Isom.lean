/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.Basic

/-!
# The isomorphism subpresheaf

For any `Cat`-valued pseudofunctor `F` and objects `x y` over `U`, the presheaf
`Isom(x, y)` is the subpresheaf of `Hom(x, y)` consisting of isomorphisms.

## Main declarations

* `CategoryTheory.Pseudofunctor.isomSubpresheaf` — `Isom(x, y)` as a `Subfunctor` of
  `presheafHom`.
-/

@[expose] public section

universe uC vC uP vP

namespace CategoryTheory

open Opposite

variable {C : Type uC} [Category.{vC} C]

namespace Pseudofunctor

variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
variable {U : C} (x y : F.obj (.mk (op U)))

/-- The presheaf `Isom(x, y)` as the subpresheaf of `Hom(x, y)` cut out by `IsIso`. -/
@[stacks 02ZB]
noncomputable def isomSubpresheaf :
    Subfunctor (F.presheafHom x y) where
  obj _ := { φ | IsIso φ }
  map g := Pseudofunctor.PresheafHom.Map.isIso F x y g

/-- Membership in the isomorphism subpresheaf is exactly `IsIso`. -/
@[simp, stacks 02ZB "isomorphism subpresheaf membership"]
theorem mem_isomSubpresheaf_iff
    {A : (Over U)ᵒᵖ}
    (φ : (F.presheafHom x y).obj A) :
    (isomSubpresheaf F x y).obj A φ ↔ IsIso φ := sorry

namespace IsomSubpresheaf

/-- Package a morphism already known to be invertible as a section of the isomorphism
subpresheaf. -/
@[stacks 02ZB "isomorphism subpresheaf section constructor"]
def mk {A : (Over U)ᵒᵖ}
    (φ : (F.presheafHom x y).obj A) [IsIso φ] :
    (isomSubpresheaf F x y).toFunctor.obj A :=
  ⟨φ, (inferInstance : IsIso φ)⟩

/-- The underlying Hom-presheaf section of `IsomSubpresheaf.mk` is the supplied morphism. -/
@[simp, stacks 02ZB "isomorphism subpresheaf section readout"]
theorem mk_val {A : (Over U)ᵒᵖ}
    (φ : (F.presheafHom x y).obj A) [IsIso φ] :
    (mk F x y φ).1 = φ := sorry

end IsomSubpresheaf

/-- For a groupoid-valued pseudofunctor every morphism is invertible, so the isomorphism
subpresheaf is the whole morphism presheaf. -/
@[simp, stacks 02ZB "groupoid-valued isomorphism subpresheaf is top"]
theorem isomSubpresheaf_eq_top
    [∀ V : C, IsGroupoid (F.obj (.mk (op V)))] :
    isomSubpresheaf F x y = ⊤ := sorry

end Pseudofunctor

end CategoryTheory
