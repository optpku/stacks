module

public import ReasLib.AlgebraicTopology.SimplicialObject.HomotopyCategory.Equiv
import StacksCheckRecall

@[expose] public section

/-!
@stack 019N

# Source-facing bridge for Definition 14.26.6

Definition 14.26.6 defines simplicial homotopy equivalences between simplicial objects.
The canonical owner declarations now live in the shared library module
`AlgebraicTopology.SimplicialObject.HomotopyEquiv`.
-/

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
variable (U V : SimplicialObject C) (a : U ⟶ V)

/- Definition 14.26.6 (1): a morphism is a homotopy equivalence when it admits a two-sided
inverse up to simplicial homotopy. -/
@[stacks 019N "Definition 14.26.6 (1): homotopy-equivalence morphism"]
#check (SimplicialObject.IsHomotopyEquivalence a : Prop)

@[stacks 019N "Definition 14.26.6 (1): explicit inverse characterization"]
#check (SimplicialObject.IsHomotopyEquivalence.iff_exists_inverse a :
  SimplicialObject.IsHomotopyEquivalence a ↔
    ∃ b : V ⟶ U,
      SimplicialObject.Homotopic (a ≫ b) (𝟙 U) ∧
        SimplicialObject.Homotopic (b ≫ a) (𝟙 V))

/- Definition 14.26.6 (2): two simplicial objects are homotopy equivalent when such data exist. -/
@[stacks 019N "Definition 14.26.6 (2): homotopy-equivalent objects"]
#check (HomRel.Equiv.nonempty_iff_exists (SimplicialObject.homotopyRel C) :
  Nonempty (SimplicialObject.HomotopyEquiv U V) ↔
    ∃ f : U ⟶ V, SimplicialObject.IsHomotopyEquivalence f)

/- The morphism predicate is exposed as a reusable morphism property. -/
#check (SimplicialObject.homotopyEquivalences C :
  MorphismProperty (SimplicialObject C))

/- The structured source presentation is the reusable relation-level data. -/
#check (HomRel.Equiv (SimplicialObject.homotopyRel C) U V : Type _)
#check HomRel.Equiv.toIso
#check SimplicialObject.IsHomotopyEquivalence.iff_exists_equiv

/- Canonically, these are exactly the maps that become isomorphisms after quotienting by
simplicial homotopy. -/
#check (SimplicialObject.HomotopyCategory.quotient.isIso_map_iff a)
