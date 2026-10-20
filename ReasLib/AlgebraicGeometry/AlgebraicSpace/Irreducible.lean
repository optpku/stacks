module

public import Mathlib.Topology.Irreducible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversalHomeomorphism

/-!
# Irreducible algebraic spaces

An algebraic space is irreducible when every canonical topology on its points
is an irreducible topological space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space is irreducible when every canonical topology on `|X|` is an
irreducible space. -/
@[mk_iff]
class IsIrreducible {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop where
  /-- Every canonical topology on `|X|` is an irreducible space. -/
  irreducibleSpace :
    ∀ (τ : TopologicalSpace (Points X)),
      IsPointsTopology X τ → @IrreducibleSpace (Points X) τ

namespace IsIrreducible

/-- An irreducible algebraic space has irreducible underlying point space in every
canonical topology. -/
theorem spec {S : Scheme.{u}} (X : AlgebraicSpace S) [IsIrreducible X]
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ) :
    @IrreducibleSpace (Points X) τ :=
  sorry

/-- Irreducibility of every canonical topology on `|X|` witnesses `IsIrreducible`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : ∀ (τ : TopologicalSpace (Points X)),
      IsPointsTopology X τ → @IrreducibleSpace (Points X) τ) :
    IsIrreducible X :=
  sorry

end IsIrreducible

/-- An irreducible scheme over `S`, viewed as an algebraic space, is irreducible. -/
instance instIsIrreducible_ofOver {S : Scheme.{u}} (U : Over S)
    [IrreducibleSpace U.left] : IsIrreducible (ofOver U) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
