/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.GroupoidScheme
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Invariant

/-!
# Invariant affine opens of groupoid schemes
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- For a groupoid scheme with finite locally free source and target maps, an orbit contained
in an affine open has an invariant affine open neighbourhood. -/
theorem exists_invariantAffineOpen {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFiniteLocallyFree G.s.left] [IsFiniteLocallyFree G.t.left]
    (u : G.U.left) (W : G.U.left.affineOpens)
    (h_orbit : G.t.left '' (G.s.left ⁻¹' {u}) ⊆ (W : Set G.U.left)) :
    ∃ V : G.U.left.affineOpens,
      u ∈ (V : G.U.left.Opens) ∧
        G.toPreRelation.IsOpenInvariant (V : G.U.left.Opens) := sorry

end AlgebraicGeometry.GroupoidScheme
