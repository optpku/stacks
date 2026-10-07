module

public import stacks_project.Chap78.Lemma_78_6_3_BaseLocus

/-!
# Maximal opens over which a group algebraic space is unramified or locally quasi-finite

A group algebraic space locally of finite type over `B` has a maximal open
subspace of `B` over which it is unramified, and a maximal open subspace of
`B` over which it is locally quasi-finite. Both commute with arbitrary base
change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace

/-- The restriction of a group algebraic space to its unramified base locus is
unramified. -/
@[stacks 0DSJ, instance]
instance instUnramified_unramifiedBaseLocus {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom] :
    AlgebraicSpace.Unramified
      (grpOverPullback G (unramifiedBaseLocus G).ι).X.hom :=
  sorry

/-- The restriction of a group algebraic space to its locally quasi-finite base
locus is locally quasi-finite. -/
@[stacks 0DSJ, instance]
instance instLocallyQuasiFinite_locallyQuasiFiniteBaseLocus {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom] :
    AlgebraicSpace.LocallyQuasiFinite
      (grpOverPullback G (locallyQuasiFiniteBaseLocus G).ι).X.hom :=
  sorry

/-- Lemma 78.6.3 (1): let `S` be a scheme, let `B` be an algebraic space over
`S`, and let `G` be a group algebraic space over `B`. Assume `G.X.hom` is
locally of finite type. Then `unramifiedBaseLocus G` is a maximal open
subspace of `B` such that the base change `G_U → U` is unramified. -/
@[stacks 0DSJ]
theorem unramifiedBaseLocus_maximal {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) [AlgebraicSpace.LocallyOfFiniteType G.X.hom]
    (V : OpenSubspace B)
    [AlgebraicSpace.Unramified (grpOverPullback G V.ι).X.hom] :
    V.pointsSet ⊆ (unramifiedBaseLocus G).pointsSet :=
  sorry

/-- Lemma 78.6.3 (2): let `S` be a scheme, let `B` be an algebraic space over
`S`, and let `G` be a group algebraic space over `B`. Assume `G.X.hom` is
locally of finite type. Formation of `unramifiedBaseLocus G` commutes with
arbitrary base change. -/
@[stacks 0DSJ]
theorem unramifiedBaseLocus_eq_preimage {S : Scheme.{u}}
    {B B' : AlgebraicSpace S} (G : GroupAlgebraicSpace B) (g : B' ⟶ B)
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom] :
    (unramifiedBaseLocus (grpOverPullback G g)).pointsSet =
      Points.map g ⁻¹' (unramifiedBaseLocus G).pointsSet :=
  sorry

/-- Lemma 78.6.3 (3): let `S` be a scheme, let `B` be an algebraic space over
`S`, and let `G` be a group algebraic space over `B`. Assume `G.X.hom` is
locally of finite type. Then `locallyQuasiFiniteBaseLocus G` is a maximal
open subspace of `B` such that the base change `G_U → U` is locally
quasi-finite. -/
@[stacks 0DSJ]
theorem locallyQuasiFiniteBaseLocus_maximal {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom] (V : OpenSubspace B)
    [AlgebraicSpace.LocallyQuasiFinite (grpOverPullback G V.ι).X.hom] :
    V.pointsSet ⊆ (locallyQuasiFiniteBaseLocus G).pointsSet :=
  sorry

/-- Lemma 78.6.3 (4): let `S` be a scheme, let `B` be an algebraic space over
`S`, and let `G` be a group algebraic space over `B`. Assume `G.X.hom` is
locally of finite type. Formation of `locallyQuasiFiniteBaseLocus G`
commutes with arbitrary base change. -/
@[stacks 0DSJ]
theorem locallyQuasiFiniteBaseLocus_eq_preimage {S : Scheme.{u}}
    {B B' : AlgebraicSpace S} (G : GroupAlgebraicSpace B) (g : B' ⟶ B)
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom] :
    (locallyQuasiFiniteBaseLocus (grpOverPullback G g)).pointsSet =
      Points.map g ⁻¹' (locallyQuasiFiniteBaseLocus G).pointsSet :=
  sorry

end AlgebraicGeometry.GroupAlgebraicSpace
