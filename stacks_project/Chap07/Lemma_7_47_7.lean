/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef

public import Mathlib.CategoryTheory.Sites.Grothendieck

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v w

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {U : C}

/- Domain-style sampling for Lemma 7.47.7:
- primary domain: closure properties of covering sieves in a Grothendieck topology;
- sampled owner API:
  `GrothendieckTopology.superset_covering`,
  `GrothendieckTopology.intersection_covering`,
  `GrothendieckTopology.intersection_covering_iff`,
  `GrothendieckTopology.transitive`;
- best owner abstraction: the covering predicate `S ∈ J U` for sieves on a fixed object;
- primitive data: the Grothendieck-topology axioms bundled in `J`;
- derived API: the order-theoretic closure theorems for covering sieves, including enlargement and
  finite intersection.

Source/core/bridge triage:
- `source-facing`: covering sieves are stable under intersection and passage to larger sieves;
- `core/canonical`: `J.intersection_covering` and `J.superset_covering`;
- `bridge/view`: the lattice/order structure on `Sieve U`, expressed by `⊓` and `≤`.

The binary intersection and enlargement clauses are direct owner theorems. The finite-intersection
form below is a small source-facing bridge over the complete-lattice structure on sieves, so later
uses do not have to rebuild the finite induction themselves.
-/

/- Lemma 7.47.7 (1): the intersection of two covering sieves on a fixed object is again covering.
This is the canonical mathlib owner theorem `GrothendieckTopology.intersection_covering`, tagged
for the corresponding Stacks clause. -/
@[stacks 00Z5] #check @intersection_covering

/-- Lemma 7.47.7 (00Z5) (1): a finite intersection of covering sieves on `U` is covering. The empty
intersection is the maximal sieve, as required by the topology axioms. -/
@[stacks 00Z5 "(1) finite intersections"]
theorem finite_iInf_covering {ι : Type w} [Finite ι]
    (S : ι → Sieve U) (hS : ∀ i, S i ∈ J U) :
    (⨅ i, S i) ∈ J U := sorry

/- Lemma 7.47.7 (2): if a sieve `S` on `U` is covering for `J` and `S ≤ S'`, then the larger
sieve `S'` is also covering. This is the canonical mathlib owner theorem
`GrothendieckTopology.superset_covering`. -/
#check @superset_covering

end CategoryTheory.GrothendieckTopology
