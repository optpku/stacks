module

public import Mathlib.Topology.Irreducible
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology

/-!
# Irreducible algebraic stacks

Irreducibility is defined on the canonical topologies of the point space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- An algebraic stack is irreducible when every canonical topology on `|X|` is
an irreducible space. -/
@[mk_iff]
class IsIrreducible {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    Prop where
  /-- Every canonical topology on `|X|` is an irreducible space. -/
  irreducibleSpace :
    ∀ (τ : TopologicalSpace (Points X)),
      IsPointsTopology X τ → @IrreducibleSpace (Points X) τ

namespace IsIrreducible

/-- An irreducible algebraic stack has irreducible underlying point space in
every canonical topology. -/
theorem spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsIrreducible X] {τ : TopologicalSpace (Points X)}
    (hτ : IsPointsTopology X τ) : @IrreducibleSpace (Points X) τ :=
  sorry

/-- Irreducibility of every canonical topology on `|X|` witnesses
`IsIrreducible`. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h : ∀ (τ : TopologicalSpace (Points X)),
      IsPointsTopology X τ → @IrreducibleSpace (Points X) τ) :
    IsIrreducible X :=
  sorry

end IsIrreducible

/-- The canonical slice of an irreducible scheme over `S` is an irreducible
algebraic stack. -/
instance instIsIrreducible_slice {S : Scheme.{u}} (U : Over S)
    [IrreducibleSpace U.left] : IsIrreducible (GroupoidsOver.slice U) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
