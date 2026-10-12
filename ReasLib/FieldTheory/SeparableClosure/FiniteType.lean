/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.Transcendence.FiniteType

/-!
# Relative Separable Closures of Finitely Generated Field Extensions

@stack 037Q

This leaf records the finite-dimensionality consequence of essential finite
type for the relative separable closure.  It is separate from the long
transcendence-basis proof of the algebraic-closure result, so field-extension
arguments can import this statement directly.
-/

@[expose] public section

universe u v

namespace FieldExtension.SeparableClosure

/-- The relative separable closure of a finite-dimensional field extension remains
finite-dimensional over the base field. -/
@[stacks 037Q "finite-dimensional field extension"]
theorem of_finiteDimensional
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] :
    FiniteDimensional k (separableClosure k K) := sorry

/-- Lemma 10.47.13 (Tag 037Q): the relative separable closure of an essentially finite type
field extension is finite-dimensional over the base field. -/
@[stacks 037Q]
theorem finiteDimensional_of_essFiniteType
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] :
    FiniteDimensional k (separableClosure k K) := sorry

end FieldExtension.SeparableClosure
