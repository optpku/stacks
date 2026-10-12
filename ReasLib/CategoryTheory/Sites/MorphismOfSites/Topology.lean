/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import ReasLib.CategoryTheory.Sites.TopologyComparison

/-!
# Topology comparisons as morphisms of sites

The identity functor becomes a morphism of sites whenever the source topology
has no more covering sieves than the target topology.
-/

@[expose] public section

universe u v

namespace CategoryTheory.IsMorphismOfSites

variable {C : Type u} [Category.{v} C] {J J' : GrothendieckTopology C}

/-- The identity functor defines a morphism of sites along an inclusion of Grothendieck
topologies. -/
theorem id_of_le (h : J' ≤ J) :
    IsMorphismOfSites J' J (𝟭 C) := sorry

end CategoryTheory.IsMorphismOfSites
