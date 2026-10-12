/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded
import Mathlib.Tactic.CrossRefAttribute

/-!
# Abelian Categories of Bounded Cochain Complexes

The bounded-below, bounded-above, and bounded object properties are closed under the finite
limit and colimit shapes needed by Mathlib's full-subcategory construction.  This leaf exposes
the corresponding kernel, cokernel, and finite-product bridges, after which the canonical
`ObjectProperty` instance supplies the abelian structures.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty

universe v u

namespace CochainComplex

variable (C : Type u) [Category.{v} C] [Abelian C]

namespace Plus

/-- Bounded-below cochain complexes are closed under kernels. -/
@[stacks 0159 "bounded-below complexes are closed under kernels"]
instance isClosedUnderKernels : (CochainComplex.plus C).IsClosedUnderKernels := sorry

/-- Bounded-below cochain complexes are closed under cokernels. -/
@[stacks 0159 "bounded-below complexes are closed under cokernels"]
instance isClosedUnderCokernels : (CochainComplex.plus C).IsClosedUnderCokernels := sorry

/-- Bounded-below cochain complexes are closed under finite products. -/
@[stacks 0159 "bounded-below complexes are closed under finite products"]
instance isClosedUnderFiniteProducts :
    (CochainComplex.plus C).IsClosedUnderFiniteProducts := sorry

end Plus

namespace Minus

/-- Bounded-above cochain complexes are closed under kernels. -/
instance isClosedUnderKernels : (CochainComplex.minus C).IsClosedUnderKernels := sorry

/-- Bounded-above cochain complexes are closed under cokernels. -/
instance isClosedUnderCokernels : (CochainComplex.minus C).IsClosedUnderCokernels := sorry

/-- Bounded-above cochain complexes are closed under finite products. -/
instance isClosedUnderFiniteProducts :
    (CochainComplex.minus C).IsClosedUnderFiniteProducts := sorry

end Minus

namespace Bounded

/-- Bounded cochain complexes are closed under kernels. -/
instance isClosedUnderKernels : (CochainComplex.bounded C).IsClosedUnderKernels := sorry

/-- Bounded cochain complexes are closed under cokernels. -/
instance isClosedUnderCokernels : (CochainComplex.bounded C).IsClosedUnderCokernels := sorry

/-- Bounded cochain complexes are closed under finite products. -/
instance isClosedUnderFiniteProducts :
    (CochainComplex.bounded C).IsClosedUnderFiniteProducts := sorry

end Bounded

end CochainComplex
