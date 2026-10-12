/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.HomPresheaf
public import ReasLib.CategoryTheory.Fibered.InGroupoids.AbelianAutomorphisms
import Mathlib.Tactic.CrossRefAttribute

/-!
# Abelian automorphisms as commuting local sections

The intrinsic abelianity class for a category fibred in groupoids can be read on every section of
its canonical local endomorphism presheaves. This characterization is independent of a topology
or a bundled stack.
-/

@[expose] public section

universe uC vC uS vS

namespace CategoryTheory

open Opposite

namespace Functor.IsFibered.InGroupoids

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]

/-- A category fibred in groupoids has abelian automorphism groups exactly when sections of every
canonical local endomorphism presheaf commute under composition. -/
@[stacks 0CJY "abelianity criterion on local sections"]
theorem Automorphism.IsAbelian.iff_sections
    (p : S ⥤ C) [Functor.IsFibered.InGroupoids p] :
    Automorphism.IsAbelian p ↔
      ∀ {U : C} (x : p.Fiber U) {T : Over U}
        (α β : ((Functor.fiberPseudofunctor p).presheafHom x x).obj (op T)),
        α ≫ β = β ≫ α := sorry

end Functor.IsFibered.InGroupoids

end CategoryTheory
