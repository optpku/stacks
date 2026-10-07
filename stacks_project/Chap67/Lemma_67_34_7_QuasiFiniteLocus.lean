module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import stacks_project.Chap66.Lemma_66_13_1_SchematicLocus
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage
public import stacks_project.Chap67.Lemma_67_23_3_Pullback
public import stacks_project.Chap67.Lemma_67_27_6_LocallyQuasiFinite
public import stacks_project.Chap67.Lemma_67_34_4_FiberDimensionLocus

/-!
# Quasi-finite locus of a locally finite-type morphism of algebraic spaces

The largest open subspace of the source on which a locally finite-type morphism
of algebraic spaces is locally quasi-finite, constructed as the subfunctor of
maps whose image of points lands in the relative-dimension-zero locus.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The subfunctor of maps into `X` whose image of points lands in the locus
where `f` has relative dimension at most `0`. -/
def quasiFiniteLocusSubfunctor {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] : Subfunctor X.functorOfPoints where
  obj U := {φ | Set.range (Points.map (ofYonedaSection φ)) ⊆ fiberDimensionLELocus f 0}
  map := sorry

/-- The algebraic space underlying the quasi-finite locus of `f`. -/
def quasiFiniteLocusSpace {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] : AlgebraicSpace S :=
  ofFunctor (quasiFiniteLocusSubfunctor f).toFunctor sorry sorry sorry

/-- The inclusion of the quasi-finite locus of `f` into `X`. -/
def quasiFiniteLocusι {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] : quasiFiniteLocusSpace f ⟶ X :=
  (quasiFiniteLocusSubfunctor f).ι

/-- The inclusion of the quasi-finite locus is an open immersion. -/
instance instIsOpenImmersion_quasiFiniteLocusι {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] :
    IsOpenImmersion (quasiFiniteLocusι f) :=
  sorry

/-- The largest open subspace of `X` on which `f` is locally quasi-finite. -/
def quasiFiniteLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] : OpenSubspace X :=
  OpenSubspace.ofι (quasiFiniteLocusι f)

/-- The inclusion of `quasiFiniteLocus f` is an open immersion. -/
instance instIsOpenImmersion_quasiFiniteLocus_ι {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] :
    IsOpenImmersion (quasiFiniteLocus f).ι :=
  (quasiFiniteLocus f).isOpenImmersion

/-- The restriction of `f` to its quasi-finite locus is locally quasi-finite. -/
instance instLocallyQuasiFinite_quasiFiniteLocus {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] :
    LocallyQuasiFinite ((quasiFiniteLocus f).ι ≫ f) :=
  sorry

/-- A point of `X` lies in the quasi-finite locus of `f` if and only if it lies
in the relative-dimension-zero locus of `f`. -/
theorem mem_quasiFiniteLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (x : Points X) :
    x ∈ Set.range (Points.map (quasiFiniteLocus f).ι) ↔ x ∈ fiberDimensionLELocus f 0 :=
  sorry

/-- A point of `X` lies in the quasi-finite locus of `f` if and only if `f` has
relative dimension at most `0` at that point. -/
theorem mem_quasiFiniteLocus_iff_relativeDimensionLEAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (x : Points X) :
    x ∈ Set.range (Points.map (quasiFiniteLocus f).ι) ↔ RelativeDimensionLEAt f 0 x :=
  sorry

/-- A point of `X` lies in the quasi-finite locus of `f` if and only if `f` is
quasi-finite at that point. -/
theorem mem_quasiFiniteLocus_iff_quasiFiniteAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (x : Points X) :
    x ∈ Set.range (Points.map (quasiFiniteLocus f).ι) ↔ QuasiFiniteAt f x :=
  sorry

/-- Any open immersion along which `f` is locally quasi-finite factors through
the quasi-finite locus on points. -/
theorem quasiFiniteLocus_maximal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] {U : AlgebraicSpace S} (i : U ⟶ X)
    [IsOpenImmersion i] (hf : LocallyQuasiFinite (i ≫ f)) :
    Set.range (Points.map i) ⊆ Set.range (Points.map (quasiFiniteLocus f).ι) :=
  sorry

/-- The quasi-finite locus is the open subspace cut out by the relative-dimension
zero subfunctor, included by an open immersion along which `f` is locally
quasi-finite, whose points are exactly the relative-dimension-zero locus. -/
theorem quasiFiniteLocus_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] :
    (quasiFiniteLocusSpace f).functorOfPoints =
        (quasiFiniteLocusSubfunctor f).toFunctor ∧
      quasiFiniteLocusι f = (quasiFiniteLocusSubfunctor f).ι ∧
      IsOpenImmersion (quasiFiniteLocusι f) ∧
      LocallyQuasiFinite ((quasiFiniteLocus f).ι ≫ f) ∧
      ∀ x : Points X,
        x ∈ Set.range (Points.map (quasiFiniteLocus f).ι) ↔ x ∈ fiberDimensionLELocus f 0 :=
  sorry

/-- If `f` is locally quasi-finite, then the quasi-finite locus occupies all of
`Points X`. -/
theorem quasiFiniteLocus_pointsSet_eq_univ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [LocallyQuasiFinite f] :
    Set.range (Points.map (quasiFiniteLocus f).ι) = Set.univ :=
  sorry

/-- The quasi-finite locus of a canonical pullback projection is the preimage of
the quasi-finite locus along the other projection. -/
theorem quasiFiniteLocus_pullback_snd {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (g : Y' ⟶ Y) [HasPullback f g] :
    Set.range (Points.map (quasiFiniteLocus (pullback.snd f g)).ι) =
      Points.map (pullback.fst f g) ⁻¹'
        Set.range (Points.map (quasiFiniteLocus f).ι) :=
  sorry

/-- In a cartesian square of algebraic spaces, the quasi-finite locus of the
base-changed morphism is the inverse image of the original quasi-finite
locus. -/
theorem quasiFiniteLocus_eq_openInverseImage_of_isPullback {S : Scheme.{u}}
    {X Y X' Y' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (hpb : IsPullback g' f' f g) [LocallyOfFiniteType f]
    [LocallyOfFiniteType f'] :
    Set.range (Points.map (quasiFiniteLocus f').ι) =
      Set.range (Points.map (openInverseImageι g' (quasiFiniteLocus f).ι)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
