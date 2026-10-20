/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition in canonical Hom-presheaves

Restriction in the canonical Hom-presheaf of a `Cat`-valued pseudofunctor
preserves composition.  This is independent of any groupoid or stack
assumption and is the reusable algebraic input for automorphism-group lifts.
-/

@[expose] public section

universe uC vC uP vP

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory

namespace Pseudofunctor

variable {C : Type uC} [Category.{vC} C]

/-- Restriction in a canonical Hom-presheaf preserves the composition of two
compatible local morphisms. -/
theorem presheafHom_map_comp
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vP, uP})
    {U : C} {x y z : F.obj (.mk (op U))}
    {W₁ W₂ : (Over U)ᵒᵖ} (f : W₁ ⟶ W₂)
    (α : (F.presheafHom x y).obj W₁)
    (β : (F.presheafHom y z).obj W₁) :
    (F.presheafHom x z).map f (α ≫ β) =
      (F.presheafHom x y).map f α ≫ (F.presheafHom y z).map f β := sorry

end Pseudofunctor

end CategoryTheory
