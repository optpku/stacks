/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Closed Equality Loci

This module packages closedness of equality loci of continuous maps into a Hausdorff target.
-/

@[expose] public section

universe u v w

namespace Continuous

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {f : X → Z} {g : Y → Z}

/-- Lemma 5.3.4: the equality locus of continuous maps from two spaces to a Hausdorff target is
closed in their product.

This is the product-domain bridge for mathlib's same-domain theorem `isClosed_eq`; it saves users
from manually composing both maps with product projections. -/
@[stacks 08ZH]
theorem isClosed_eqLocus_prod [T2Space Z] (hf : Continuous f) (hg : Continuous g) :
    IsClosed {p : X × Y | f p.1 = g p.2} := sorry

/-- Lemma 5.3.2, tag 08ZF: the graph map of a continuous map into a Hausdorff space is a closed
embedding.

Mathlib already provides its inducing and injectivity part as `isEmbedding_graph`. -/
@[stacks 08ZF]
theorem isClosedEmbedding_graph {f : X → Y} [T2Space Y] (hf : Continuous f) :
    Topology.IsClosedEmbedding fun x => (x, f x) := sorry

/-- Lemma 5.3.2, tag 08ZF: the set-level closed-graph form of `isClosedEmbedding_graph`. -/
@[stacks 08ZF]
theorem isClosed_graph {f : X → Y} [T2Space Y] (hf : Continuous f) :
    IsClosed (Set.univ.graphOn f) := sorry

end Continuous
