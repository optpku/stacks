module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.AffineOpen.DimensionOne
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 40.14.10: if the source and target maps of a groupoid scheme are finite, its
object scheme is separated and locally Noetherian, and every point in the orbit of `u` has
stalk dimension at most one, then `u` has an invariant affine open neighbourhood. -/
@[stacks 0ABI] #check
  (AlgebraicGeometry.GroupoidScheme.exists_invariantAffineOpen_of_orbit_stalkDimensionLEOne :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S) [IsFinite G.s.left] [IsFinite G.t.left]
      [Scheme.IsSeparated G.U.left] [IsLocallyNoetherian G.U.left] (u : G.U.left)
      (h_dim : let X := G.U.left
        ∀ u' ∈ G.t.left '' (G.s.left ⁻¹' {u}), ringKrullDim (X.presheaf.stalk u') ≤ 1),
      ∃ V : G.U.left.affineOpens,
        u ∈ (V : Scheme.Opens G.U.left) ∧
          G.toPreRelation.IsOpenInvariant (V : Scheme.Opens G.U.left))
