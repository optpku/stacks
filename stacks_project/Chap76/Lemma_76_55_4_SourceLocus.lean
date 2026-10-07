module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Topology.Sets.Opens
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap67.Remark_67_12_5_Opens
public import stacks_project.Chap76.Definition_76_55_1_AtWorstNodal

/-!
# At-worst-nodal source locus of a morphism of algebraic spaces

The largest open subspace of the source on which a morphism of algebraic spaces
is at-worst-nodal of relative dimension 1, constructed as the open subspace cut
out by the supremum of opens of `Points X` on which the restriction has the
property.
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
    AtWorstNodal ((OpenSubspace.ofOpens W).ι ≫ f))

/-- The largest open subspace of `X` on which `f` is at-worst-nodal of relative
dimension 1. -/
def sourceLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    OpenSubspace X :=
  OpenSubspace.ofOpens (sourceLocusOpens f)

/-- The inclusion of `sourceLocus f` is an open immersion. -/
instance instIsOpenImmersion_sourceLocus_ι {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    IsOpenImmersion (sourceLocus f).ι :=
  (sourceLocus f).isOpenImmersion

/-- The restriction of a flat, locally finitely presented morphism to its
at-worst-nodal source locus is at-worst-nodal of relative dimension 1. -/
instance instAtWorstNodal_sourceLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] :
    AtWorstNodal ((sourceLocus f).ι ≫ f) :=
  sorry

/-- The underlying point-set of `sourceLocus f` is `sourceLocusOpens f`. -/
theorem sourceLocus_pointsSet_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    (sourceLocus f).pointsSet = sourceLocusOpens f :=
  sorry

/-- A point of `X` lies in `sourceLocusOpens f` if and only if it lies in some
open of `Points X` on which the restriction of `f` is at-worst-nodal of relative
dimension 1. -/
theorem mem_sourceLocusOpens {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) :
    x ∈ sourceLocusOpens f ↔
      ∃ W : Opens (Points X),
        x ∈ W ∧ AtWorstNodal ((OpenSubspace.ofOpens W).ι ≫ f) :=
  sorry

/-- Any open immersion along which `f` is at-worst-nodal of relative dimension 1
factors through the at-worst-nodal source locus on points. -/
theorem sourceLocus_maximal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {U : AlgebraicSpace S} (i : U ⟶ X) [IsOpenImmersion i]
    (hf : AtWorstNodal (i ≫ f)) :
    Set.range (Points.map i) ⊆ (sourceLocus f).pointsSet :=
  sorry

/-- For a flat, locally finitely presented morphism, `sourceLocusOpens f` is the
greatest open of `Points X` on which the restriction of `f` is at-worst-nodal of
relative dimension 1. -/
theorem sourceLocusOpens_isGreatest {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] :
    IsGreatest (setOf fun W : Opens (Points X) ↦
        AtWorstNodal ((OpenSubspace.ofOpens W).ι ≫ f))
      (sourceLocusOpens f) :=
  sorry

/-- The at-worst-nodal source locus occupies `sourceLocusOpens f`, its inclusion
is an open immersion, the restriction of a flat locally finitely presented
morphism along it is at-worst-nodal of relative dimension 1, and it contains
every open immersion with that property. -/
theorem sourceLocus_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] :
    (sourceLocus f).pointsSet = sourceLocusOpens f ∧
      IsOpenImmersion (sourceLocus f).ι ∧
      AtWorstNodal ((sourceLocus f).ι ≫ f) ∧
      ∀ {U : AlgebraicSpace S} (i : U ⟶ X) [IsOpenImmersion i],
        AtWorstNodal (i ≫ f) →
          Set.range (Points.map i) ⊆ (sourceLocus f).pointsSet :=
  sorry

/-- The at-worst-nodal source locus of a canonical pullback projection is the
preimage of the original source locus along the other projection. -/
theorem sourceLocus_pullback_snd {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] (g : Y' ⟶ Y) :
    (sourceLocus (pullback.snd f g)).pointsSet =
      Points.map (pullback.fst f g) ⁻¹' (sourceLocus f).pointsSet :=
  sorry

/-- In a cartesian square of algebraic spaces, the at-worst-nodal source locus of
the base-changed morphism is the inverse image open of the original source
locus. -/
theorem sourceLocus_eq_openInverseImage_of_isPullback {S : Scheme.{u}}
    {X Y X' Y' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g) [Flat f]
    [LocallyOfFinitePresentation f] :
    (sourceLocus f').pointsSet =
      Set.range (Points.map (openInverseImageι g' (sourceLocus f).ι)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.AtWorstNodal
