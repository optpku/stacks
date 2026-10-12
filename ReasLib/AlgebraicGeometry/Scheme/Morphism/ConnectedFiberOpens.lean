/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.Connected.Basic

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Every nonempty open of each fibre of a scheme morphism is connected. -/
def HasConnectedFiberOpens {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ (s : S) (U : (f.fiber s).Opens), U.1.Nonempty →
    _root_.IsConnected (U : Set (f.fiber s))

/-- Irreducible or empty fibres have connected nonempty open subsets. -/
theorem hasConnectedFiberOpens_of_irreducible {X S : Scheme.{u}} (f : X ⟶ S)
    (h : ∀ s : S, IsEmpty (f.fiber s) ∨ IrreducibleSpace (f.fiber s)) :
    HasConnectedFiberOpens f := sorry

end AlgebraicGeometry.Scheme.Hom
