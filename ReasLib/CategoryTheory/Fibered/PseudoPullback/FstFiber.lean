/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.FstFiber.Basic
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.FstFiber.FromFiber
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.FstFiber.Equivalence
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.FstFiber.Computations

/-!
# A structured-arrow model for a fibre of a pseudo-pullback projection

This aggregate import exposes the structured-arrow description of the fibre of the first
pseudo-pullback projection. The implementation is organized by mathematical layer:

* Basic: the structured-arrow category, its comparison functor, and foundational formulas;
* FromFiber: the inverse comparison functor and its direct component formulas;
* Equivalence: unit, counit, quasi-inverse data, and the canonical equivalence;
* Computations: stable formulas for unit/counit components and packaged equivalence data.

New developments should import the smallest leaf that supplies their required API. This aggregate
remains the broad entry point. The public surface is organized directly under
`BasedCategory.PseudoPullback.FstFiber`: `comparison` and `comparisonInverse` own the two
functors and their readouts; `StructuredArrow.homEquiv` and `StructuredArrow.homEquivInv` own
the reusable structured-arrow morphism API, while `exists_hom_right_iff_map_eq` records its
groupoid-fibre specialization; and `comparison.unitIso`,
`comparison.counitIso`, `comparison.quasiInverse`, and `comparison.equivalence` package the
coherence.
-/
