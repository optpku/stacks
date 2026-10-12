/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FiniteFree
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.CrossRefAttribute

/-!
# Free modules of rank one

The property in this file does not choose a basis: a bundled module is free of rank one when it
is isomorphic to the tensor unit.  This categorical formulation is stable under isomorphism and
is the right input for tensor, finiteness, and rank calculations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

universe u

namespace CategoryTheory.ModuleCat

variable (R : Type u) [CommRing R]

/-- Bundled modules which are isomorphic to the tensor unit, equivalently free modules of rank
one without a chosen basis. -/
@[stacks 0GTA "free rank-one module property"]
def freeRankOne : ObjectProperty (ModuleCat R) :=
  fun L => IsIsomorphic L (𝟙_ (ModuleCat R))

/-- The defining characterization of the free rank-one module property. -/
theorem mem_freeRankOne_iff (L : ModuleCat R) :
    freeRankOne R L ↔ IsIsomorphic L (𝟙_ (ModuleCat R)) := sorry

/-- Being free of rank one is invariant under isomorphism. -/
instance freeRankOne.isClosedUnderIsomorphisms :
    (freeRankOne R).IsClosedUnderIsomorphisms := sorry

/-- A free rank-one module is finite free. -/
@[stacks 0GTA "free rank one implies finite free"]
theorem freeRankOne_le_finiteFree :
    freeRankOne R ≤ finiteFree R := sorry

namespace freeRankOne

variable {R}

/-- Tensoring on the right by a free rank-one module does not change an object up to
isomorphism. -/
@[stacks 0GTA "tensor by a free rank-one module"]
theorem tensorRight_isomorphic {L M : ModuleCat R} (hL : freeRankOne R L) :
    IsIsomorphic (M ⊗ L) M := sorry

/-- Tensoring on the right by a free rank-one module preserves and reflects finite freeness. -/
@[stacks 0GTA "finite free under rank-one tensor"]
theorem finiteFree_tensorRight_iff {L M : ModuleCat R} (hL : freeRankOne R L) :
    finiteFree R (M ⊗ L) ↔ finiteFree R M := sorry

/-- Over a nonzero commutative ring, tensoring on the right by a free rank-one module preserves
module rank. -/
@[stacks 0GTA "rank under rank-one tensor"]
theorem rank_tensorRight_eq [Nontrivial R] {L M : ModuleCat R} (hL : freeRankOne R L) :
    Module.rank R (M ⊗ L : ModuleCat R) = Module.rank R M := sorry

end freeRankOne

end CategoryTheory.ModuleCat
