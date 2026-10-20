module

public import Mathlib.Order.Bounds.Basic
public import Mathlib.Topology.Sets.Opens
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.AtWorstNodal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# At-worst-nodal source loci of morphisms of algebraic spaces

The source locus is constructed from the supremum of opens on which the
restriction is at-worst-nodal of relative dimension 1. For flat, locally finitely
presented morphisms, it is the largest such open and commutes with arbitrary
base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.Limits
  TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AtWorstNodal

/-- The supremum of the opens of `Points X` on which the restriction of `f` is
at-worst-nodal of relative dimension 1. -/
def sourceLocusOpens {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Opens (Points X) :=
  sSup (setOf fun W : Opens (Points X) ↦
    AtWorstNodal ((OpenSubspace.fromOpens W).ι ≫ f))

/-- The open subspace determined by the supremum of opens on which `f` is
at-worst-nodal of relative dimension 1. -/
def sourceLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    OpenSubspace X :=
  OpenSubspace.fromOpens (sourceLocusOpens f)

/-- The inclusion of the at-worst-nodal source locus is an open immersion. -/
def sourceLocus_isOpenImmersion {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    IsOpenImmersion (sourceLocus f).ι :=
  (sourceLocus f).isOpenImmersion

/-- The underlying point set of the source locus is its defining open set. -/
theorem sourceLocus_pointsSet_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    (sourceLocus f).pointsSet = sourceLocusOpens f :=
  OpenSubspace.fromOpens_pointsSet (sourceLocusOpens f)

/-- A point lies in the source locus open if and only if it lies in an open on
which the restriction is at-worst-nodal of relative dimension 1. -/
theorem mem_sourceLocusOpens {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) :
    x ∈ sourceLocusOpens f ↔
      ∃ W : Opens (Points X),
        x ∈ W ∧ AtWorstNodal ((OpenSubspace.fromOpens W).ι ≫ f) :=
  sorry

/-- Every open immersion along which a morphism is at-worst-nodal of relative
dimension 1 has point image contained in its source locus. -/
theorem sourceLocus_maximal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {U : AlgebraicSpace S} (i : U ⟶ X) [IsOpenImmersion i]
    (hf : AtWorstNodal (i ≫ f)) :
    Set.range (Points.map i) ⊆ (sourceLocus f).pointsSet :=
  sorry

/-- A flat, locally finitely presented morphism is at-worst-nodal of relative
dimension 1 on its source locus, and every open immersion with this property
has point image contained in that locus. -/
theorem sourceLocus_isLargest {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] :
    AtWorstNodal ((sourceLocus f).ι ≫ f) ∧
      ∀ {U : AlgebraicSpace S} (i : U ⟶ X) [IsOpenImmersion i],
        AtWorstNodal (i ≫ f) →
          Set.range (Points.map i) ⊆ (sourceLocus f).pointsSet :=
  sorry

/-- The restriction of a flat, locally finitely presented morphism to its
source locus is at-worst-nodal of relative dimension 1. -/
def sourceLocus_atWorstNodal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] :
    AtWorstNodal ((sourceLocus f).ι ≫ f) :=
  (sourceLocus_isLargest f).1

/-- For a flat, locally finitely presented morphism, the source locus open is
the greatest open on which the restriction is at-worst-nodal of relative
dimension 1. -/
theorem sourceLocusOpens_isGreatest {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] :
    IsGreatest (setOf fun W : Opens (Points X) ↦
        AtWorstNodal ((OpenSubspace.fromOpens W).ι ≫ f))
      (sourceLocusOpens f) :=
  sorry

/-- The source locus has its defining point set and an open immersion inclusion;
for a flat, locally finitely presented morphism, its restriction is at-worst-nodal
of relative dimension 1 and it contains every open immersion with this property. -/
theorem sourceLocus_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] :
    (sourceLocus f).pointsSet = sourceLocusOpens f ∧
      IsOpenImmersion (sourceLocus f).ι ∧
      AtWorstNodal ((sourceLocus f).ι ≫ f) ∧
      ∀ {U : AlgebraicSpace S} (i : U ⟶ X) [IsOpenImmersion i],
        AtWorstNodal (i ≫ f) →
          Set.range (Points.map i) ⊆ (sourceLocus f).pointsSet :=
  ⟨sourceLocus_pointsSet_eq f, sourceLocus_isOpenImmersion f, sourceLocus_isLargest f⟩

/-- Formation of the at-worst-nodal source locus of a flat, locally finitely
presented morphism commutes with arbitrary cartesian base change. -/
theorem sourceLocus_eq_preimage_of_isPullback {S : Scheme.{u}}
    {X Y X' Y' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g) [Flat f]
    [LocallyOfFinitePresentation f] :
    (sourceLocus f').pointsSet = Points.map g' ⁻¹' (sourceLocus f).pointsSet :=
  sorry

/-- The at-worst-nodal source locus of a canonical pullback projection is the
preimage of the original source locus along the other projection. -/
theorem sourceLocus_pullback_snd {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] (g : Y' ⟶ Y) :
    (sourceLocus (pullback.snd f g)).pointsSet =
      Points.map (pullback.fst f g) ⁻¹' (sourceLocus f).pointsSet :=
  sourceLocus_eq_preimage_of_isPullback (pullback.fst f g) (pullback.snd f g)
    f g (IsPullback.of_hasPullback f g)

end AlgebraicGeometry.AlgebraicSpace.AtWorstNodal
