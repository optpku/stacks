/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Graph.Counit
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Graph.Unit
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Bicategorical
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalence induced by the graph into an identity pseudo-pullback

This leaf assembles the graph unit and counit into explicit quasi-inverse data, the stable-universe
bicategorical equivalence, and the reusable `BasedFunctor.IsEquivalence` instance.
-/

@[expose] public section

universe w u v vB uX vX uY vY

namespace CategoryTheory
namespace BasedCategory.PseudoPullback

open Functor.Fiber
open scoped BasedFunctor

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}

noncomputable section

/-- Explicit quasi-inverse data for the graph into an identity pseudo-pullback. The inverse is
the first projection, and the counit is induced by each object's structural isomorphism. -/
@[stacks 0040 "explicit graph quasi-inverse"]
noncomputable def graph.quasiInverse (F : X ⥤ᵇ Y) :
    BasedFunctor.QuasiInverse (graph F) where
  inverse := PseudoPullback.fst F (𝟭 Y)
  unitIso := graph.unitIso F
  counitIso := graph.counitIso F

/-- The inverse in the explicit graph quasi-inverse data is the first projection. -/
@[simp]
theorem graph.quasiInverse.inverse (F : X ⥤ᵇ Y) :
    (graph.quasiInverse F).inverse = PseudoPullback.fst F (𝟭 Y) := sorry

/-- The unit in the explicit graph quasi-inverse data is the canonical identity-to-graph
isomorphism. -/
@[simp]
theorem graph.quasiInverse.unitIso (F : X ⥤ᵇ Y) :
    (graph.quasiInverse F).unitIso = graph.unitIso F := sorry

/-- The counit in the explicit graph quasi-inverse data is induced by the structural
isomorphisms of pseudo-pullback objects. -/
@[simp]
theorem graph.quasiInverse.counitIso (F : X ⥤ᵇ Y) :
    (graph.quasiInverse F).counitIso = graph.counitIso F := sorry

section StableUniverse

variable
  {X₀ Y₀ : BasedCategory.{max v vB, max w (max u (max v vB))} C}

/-- On a stable universe layer, the graph quasi-inverse data package into the canonical
bicategorical equivalence over the base. For genuinely heterogeneous universes, use
`graph.quasiInverse`. -/
@[stacks 0040 "equivalence with an explicit pseudo-pullback along an identity leg"]
noncomputable def graph.equivalence (F : X₀ ⥤ᵇ Y₀) :
    Bicategory.Equivalence X₀ (PseudoPullback F (𝟭 Y₀)) :=
  (graph.quasiInverse F).toEquivalence

/-- The forward morphism of the based graph equivalence is the explicit graph. -/
@[simp]
theorem graph.equivalence.hom (F : X₀ ⥤ᵇ Y₀) :
    (graph.equivalence F).hom = graph F := sorry

/-- The inverse morphism of the based graph equivalence is the first pseudo-pullback
projection. -/
@[simp]
theorem graph.equivalence.inv (F : X₀ ⥤ᵇ Y₀) :
    (graph.equivalence F).inv = PseudoPullback.fst F (𝟭 Y₀) := sorry

/-- The unit of the based graph equivalence is the canonical adjustment of the explicit graph
unit against the explicit graph counit. -/
@[simp]
theorem graph.equivalence.unit (F : X₀ ⥤ᵇ Y₀) :
    (graph.equivalence F).unit =
      Bicategory.Equivalence.adjointifyUnit
        (graph.unitIso F) (graph.counitIso F) := sorry

/-- The counit of the based graph equivalence is the explicit graph counit. -/
@[simp]
theorem graph.equivalence.counit (F : X₀ ⥤ᵇ Y₀) :
    (graph.equivalence F).counit = graph.counitIso F := sorry

end StableUniverse

/-- The graph into an identity pseudo-pullback is an equivalence over the base. -/
@[stacks 0040 "graph equivalence instance"]
instance graph.isEquivalence (F : X ⥤ᵇ Y) : (graph F).IsEquivalence := sorry
/- Proof strategy: use `fst F (𝟭 Y)` as quasi-inverse. The unit is componentwise the identity;
the counit uses the comparison isomorphism stored by each pseudo-pullback object. -/

/- Data audit: `#print axioms` for `graph`, `graph.quasiInverse`, and `graph.equivalence` reports
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. Their constructors above show that
the object and morphism actions, inverse functor, and unit/counit component isomorphisms are
explicit. The `sorryAx` dependencies occur in membership, lift, naturality, functor-law, and
equivalence-coherence proof fields rather than selecting any of this non-`Prop` data. -/

end

end BasedCategory.PseudoPullback
end CategoryTheory
