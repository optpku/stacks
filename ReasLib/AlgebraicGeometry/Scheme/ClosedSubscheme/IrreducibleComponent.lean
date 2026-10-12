/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Topology.Irreducible
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Reduced

/-!
# Reduced subschemes of irreducible components

This leaf gives the canonical reduced closed subscheme associated to an
irreducible component.  It is independent of any Galois or finite-type
argument that later acts on the component set.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme

noncomputable section

/-- The irreducible closed subset of `X` carried by an irreducible component. -/
@[stacks 0G42 "irreducible component as an irreducible closed subset"]
abbrev irreducibleComponentIrreducibleClosed
    (X : Scheme.{u}) (Z : irreducibleComponents X) :
    TopologicalSpace.IrreducibleCloseds X :=
  ⟨(Z : Set X), Z.2.1, isClosed_of_mem_irreducibleComponents (Z : Set X) Z.2⟩

/-- The closed subset of `X` underlying an irreducible component. -/
@[stacks 0G42 "closed subset of an irreducible component"]
abbrev irreducibleComponentClosed (X : Scheme.{u}) (Z : irreducibleComponents X) :
    TopologicalSpace.Closeds X :=
  ⟨(Z : Set X), isClosed_of_mem_irreducibleComponents (Z : Set X) Z.2⟩

/-- Membership in the closed subset attached to an irreducible component. -/
@[simp, stacks 0G42]
theorem mem_irreducibleComponentClosed
    (X : Scheme.{u}) (Z : irreducibleComponents X) (x : X) :
    x ∈ X.irreducibleComponentClosed Z ↔ x ∈ (Z : Set X) := sorry

/-- The reduced induced closed subscheme attached to an irreducible component. -/
@[stacks 0G42 "reduced irreducible-component subscheme"]
abbrev irreducibleComponentSubscheme (X : Scheme.{u}) (Z : irreducibleComponents X) :
    Scheme.{u} :=
  (IdealSheafData.vanishingIdeal (X.irreducibleComponentClosed Z)).subscheme

namespace IrreducibleComponent

/-- The reduced subscheme carried by an irreducible component is irreducible. -/
instance instIrreducibleSpace
    (X : Scheme.{u}) (Z : irreducibleComponents X) :
    IrreducibleSpace (X.irreducibleComponentSubscheme Z) := sorry

end IrreducibleComponent

/-- The canonical immersion from the irreducible-component subscheme into `X`. -/
@[stacks 0G42 "irreducible-component subscheme immersion"]
abbrev irreducibleComponentSubschemeι (X : Scheme.{u}) (Z : irreducibleComponents X) :
    X.irreducibleComponentSubscheme Z ⟶ X :=
  (IdealSheafData.vanishingIdeal (X.irreducibleComponentClosed Z)).subschemeι

end

end Scheme
end AlgebraicGeometry
