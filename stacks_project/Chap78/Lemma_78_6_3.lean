module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group.BaseLocus
import StacksCheckRecall

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

open AlgebraicGeometry.GroupAlgebraicSpace

/- Lemma 78.6.3 (1): the restriction to the unramified base locus is unramified. -/
@[stacks 0DSJ] #check
  (AlgebraicGeometry.GroupAlgebraicSpace.instUnramified_unramifiedBaseLocus :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
      [AlgebraicSpace.LocallyOfFiniteType G.X.hom],
    AlgebraicSpace.Unramified
      (baseChange G (unramifiedBaseLocus G).ι).X.hom)

/- Lemma 78.6.3 (2): the restriction to the locally quasi-finite base locus is
locally quasi-finite. -/
@[stacks 0DSJ] #check
  (AlgebraicGeometry.GroupAlgebraicSpace.instLocallyQuasiFinite_locallyQuasiFiniteBaseLocus :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
      [AlgebraicSpace.LocallyOfFiniteType G.X.hom],
    AlgebraicSpace.LocallyQuasiFinite
      (baseChange G (locallyQuasiFiniteBaseLocus G).ι).X.hom)

/- Lemma 78.6.3 (1): every open over which the group is unramified is contained
in the unramified base locus. -/
@[stacks 0DSJ] #check
  (AlgebraicGeometry.GroupAlgebraicSpace.unramifiedBaseLocus_maximal :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
      [AlgebraicSpace.LocallyOfFiniteType G.X.hom] (V : OpenSubspace B)
      [AlgebraicSpace.Unramified (baseChange G V.ι).X.hom],
    V.pointsSet ⊆ (unramifiedBaseLocus G).pointsSet)

/- Lemma 78.6.3 (1): formation of the unramified base locus commutes with
arbitrary base change. -/
@[stacks 0DSJ] #check
  (AlgebraicGeometry.GroupAlgebraicSpace.unramifiedBaseLocus_eq_preimage :
    ∀ {S : Scheme.{u}} {B B' : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
      (g : B' ⟶ B) [AlgebraicSpace.LocallyOfFiniteType G.X.hom],
    (unramifiedBaseLocus (baseChange G g)).pointsSet =
      Points.map g ⁻¹' (unramifiedBaseLocus G).pointsSet)

/- Lemma 78.6.3 (2): every open over which the group is locally quasi-finite is
contained in the locally quasi-finite base locus. -/
@[stacks 0DSJ] #check
  (AlgebraicGeometry.GroupAlgebraicSpace.locallyQuasiFiniteBaseLocus_maximal :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
      [AlgebraicSpace.LocallyOfFiniteType G.X.hom] (V : OpenSubspace B)
      [AlgebraicSpace.LocallyQuasiFinite (baseChange G V.ι).X.hom],
    V.pointsSet ⊆ (locallyQuasiFiniteBaseLocus G).pointsSet)

/- Lemma 78.6.3 (2): formation of the locally quasi-finite base locus commutes
with arbitrary base change. -/
@[stacks 0DSJ] #check
  (AlgebraicGeometry.GroupAlgebraicSpace.locallyQuasiFiniteBaseLocus_eq_preimage :
    ∀ {S : Scheme.{u}} {B B' : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
      (g : B' ⟶ B) [AlgebraicSpace.LocallyOfFiniteType G.X.hom],
    (locallyQuasiFiniteBaseLocus (baseChange G g)).pointsSet =
      Points.map g ⁻¹' (locallyQuasiFiniteBaseLocus G).pointsSet)
