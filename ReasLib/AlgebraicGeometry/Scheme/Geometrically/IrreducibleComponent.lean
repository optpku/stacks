module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Connected.Clopen
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent
public import ReasLib.Topology.ConnectedComponents.Finite

/-!
# Geometric irreducibility of irreducible components

This leaf records the property that every irreducible component, equipped with
its canonical reduced induced closed-subscheme structure, is geometrically
irreducible over a field.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat

universe u

namespace AlgebraicGeometry

namespace GeometricallyIrreducible.Components

/-- Every irreducible component of the source, with its reduced induced closed-subscheme
structure, is geometrically irreducible over the base field. -/
def all
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) : Prop :=
  ∀ Z : irreducibleComponents X,
    GeometricallyIrreducible (X.irreducibleComponentSubschemeι Z ≫ f)

/-- `all f` unfolds to geometric irreducibility of the canonical reduced component subschemes. -/
theorem all_iff
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) :
    all f ↔
      ∀ Z : irreducibleComponents X,
        GeometricallyIrreducible (X.irreducibleComponentSubschemeι Z ≫ f) := sorry

/-- A scheme with finitely many irreducible components whose canonical reduced components are
geometrically irreducible has finitely many connected components. -/
@[stacks 054S]
theorem finiteConnectedComponents
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))
    [Finite (irreducibleComponents X)]
    (hgeom : all f) :
    Finite (ConnectedComponents X) := sorry

end GeometricallyIrreducible.Components

end AlgebraicGeometry
