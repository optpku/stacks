/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.FixedPseudoPullback.Comparison.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.FixedPseudoPullback.Comparison.Computations

/-!
# Fixed groupoid-fibred relative-inertia comparison

Aggregate for the fixed relative-inertia diagonal comparison. `Construction`
owns the comparison and fibredness bridge; `Computations` owns its projection
readouts. Import the smallest leaf required by new developments.
-/

@[expose] public section
