/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FreeForgetResolution.Generators.FiniteSums
import StacksCheckRecall

@[expose] public section

/-!
@stack 0G5U

# Low-degree maps in the free-module resolution

This file is the source-facing facade for Example 14.34.6.  The canonical maps, their
generator formulas, and the finite-sum corollaries are owned by
`CategoryTheory.ModuleCat.FreeForgetResolution`.
-/

open CategoryTheory
open scoped CategoryTheory.IteratedEndofunctor

universe u uι uκ

noncomputable section

namespace CategoryTheory.ModuleCat.FreeForgetResolution

variable (R : Type u) [Ring R] (M : ModuleCat.{u} R)
variable {I : Type uι} {J : I → Type uκ} [Fintype I] [∀ i, Fintype (J i)]
variable (r : I → R) (s : ∀ i, J i → R) (m : ∀ i, J i → M)
variable (x : (functor R).obj M)

#check (face R 0 (1 : Fin 2) : (functor R) ⁺⦋1⦌ ⟶ (functor R) ⁺⦋0⦌)
#check (degeneracy R 1 (1 : Fin 2) : (functor R) ⁺⦋1⦌ ⟶ (functor R) ⁺⦋2⦌)
#check (face.zero.freeMk M x :
  (face R 0 (1 : Fin 2)).app M (ModuleCat.freeMk x) = x)
#check (face.one.freeMk M x :
  (face R 0 (0 : Fin 2)).app M (ModuleCat.freeMk x) =
    ModuleCat.freeMk ((counit R).app M x))
#check (degeneracy.zero.freeMk M x :
  (degeneracy R 1 (1 : Fin 2)).app M (ModuleCat.freeMk x) =
    ModuleCat.freeMk (ModuleCat.freeMk x))
#check (degeneracy.one.freeMk M x :
  (degeneracy R 1 (0 : Fin 2)).app M (ModuleCat.freeMk x) =
    ModuleCat.freeMk ((comultiplication R).app M x))

/- Example 14.34.6 (1): the zeroth face flattens both free-module layers and multiplies their
coefficients. -/
@[stacks 0G5U "Example 14.34.6 (1)"]
#check (face.zero.nestedSum M r s m :
  (face R 0 (1 : Fin 2)).app M
      (∑ i, r i • ModuleCat.freeMk (∑ j, s i j • ModuleCat.freeMk (m i j))) =
    ∑ i, ∑ j, (r i * s i j) • ModuleCat.freeMk (m i j))

/- Example 14.34.6 (2): the first face evaluates the inner free-module layer. -/
@[stacks 0G5U "Example 14.34.6 (2)"]
#check (face.one.nestedSum M r s m :
  (face R 0 (0 : Fin 2)).app M
      (∑ i, r i • ModuleCat.freeMk (∑ j, s i j • ModuleCat.freeMk (m i j))) =
    ∑ i, r i • ModuleCat.freeMk (∑ j, s i j • m i j))

/- Example 14.34.6 (3): the zeroth degeneracy inserts an outer free-module bracket. -/
@[stacks 0G5U "Example 14.34.6 (3)"]
#check (degeneracy.zero.nestedSum M r s m :
  (degeneracy R 1 (1 : Fin 2)).app M
      (∑ i, r i • ModuleCat.freeMk (∑ j, s i j • ModuleCat.freeMk (m i j))) =
    ∑ i, r i • ModuleCat.freeMk
      (ModuleCat.freeMk (∑ j, s i j • ModuleCat.freeMk (m i j))))

/- Example 14.34.6 (4): the first degeneracy inserts brackets at the inner layer. -/
@[stacks 0G5U "Example 14.34.6 (4)"]
#check (degeneracy.one.nestedSum M r s m :
  (degeneracy R 1 (0 : Fin 2)).app M
      (∑ i, r i • ModuleCat.freeMk (∑ j, s i j • ModuleCat.freeMk (m i j))) =
    ∑ i, r i • ModuleCat.freeMk
      (∑ j, s i j • ModuleCat.freeMk (ModuleCat.freeMk (m i j))))

end CategoryTheory.ModuleCat.FreeForgetResolution
