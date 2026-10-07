module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import ReasLib.Algebra.Category.ModuleCat.Finite
public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite presentation of module cokernels

The primary theorem uses the weakest natural hypotheses: the source of the module map is finitely
generated and its target is finitely presented.  Closure of the finitely presented object property
under cokernels is then a canonical instance rather than a separate source-specific construction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u v

namespace ModuleCat.isFinitePresentation

variable {R : Type u} [Ring R]
variable {M N : ModuleCat.{v} R}

/-- A cokernel is finitely presented when the source of the map is finitely generated and its
target is finitely presented. -/
@[stacks 0519 "finite presentation of module cokernels"]
theorem cokernel_of_isFG (f : M ⟶ N)
    (hM : ModuleCat.isFG R M)
    (hN : ModuleCat.isFinitePresentation R N) :
    ModuleCat.isFinitePresentation R (cokernel f) :=
  cokernel_of_finite (R := R) f hM hN

end ModuleCat.isFinitePresentation
