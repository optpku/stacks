/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap62.Example_62_7_2_Family
public import stacks_project.Chap62.Lemma_62_6_6_Relative
import Mathlib.Tactic.CrossRefAttribute

/-!
# Example 62.7.2

A relative 0-cycle on the affine line over the affine plane which is compatible
with specializations, but whose support closure contains the origin fibre and
so is not equidimensional.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Scheme.Hom
open CyclesOnFibers
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AffineLineOverPlane

/-- Example 62.7.2 (1): the family `α` of 0-cycles on `X / S` is a relative
0-cycle, i.e. compatible with specializations. The heuristic is that `a / b`
and `(a + b²) / b = a / b + b` limit to the same point of `ℙ¹` over the
residue field of any valuation `v` on `κ(s)` with `v(b) > 0`. -/
@[stacks 0H5J]
theorem family_isRelative (k : Type u) [Field k] :
    RelativeCycle.IsRelative (family k) :=
  sorry

/-- Example 62.7.2 (2): the closure of the support of `α` contains the whole
fibre over the origin `(0, 0)`. -/
@[stacks 0H5J]
theorem closure_support_contains_originFiber (k : Type u) [Field k] :
    Set.range ((hom k).fiberι (origin k)) ⊆
      closure (CyclesOnFibers.support (family k)) :=
  sorry

/-- Example 62.7.2 (3): the family `α` is not equidimensional: its support is
not contained in any closed subscheme of relative dimension at most `0` over
`S`. -/
@[stacks 0H5J]
theorem not_equidimensional (k : Type u) [Field k] :
    ¬ Equidimensional (family k) :=
  sorry

end AlgebraicGeometry.AffineLineOverPlane
