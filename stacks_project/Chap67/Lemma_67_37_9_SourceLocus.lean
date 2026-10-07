module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap67.Lemma_67_37_4_Smooth

/-!
# Smooth source locus of a morphism of algebraic spaces

The largest open subspace of the source on which a morphism of algebraic spaces
is smooth, constructed as the subfunctor of maps whose image of points lands in
the pointwise smooth locus.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The morphism of algebraic spaces associated to a Yoneda section of `X`. -/
def functorOfPointsHom {S : Scheme.{u}} {X : AlgebraicSpace S} {U : (Over S)ᵒᵖ}
    (α : X.functorOfPoints.obj U) : ofOver U.unop ⟶ X :=
  yonedaEquiv.symm α

/-- The subfunctor of maps into `X` whose image of points lands in the smooth
locus of `f`. -/
def sourceLocusSubfunctor {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Subfunctor X.functorOfPoints where
  obj U := {φ | Set.range (Points.map (functorOfPointsHom φ)) ⊆ {x | SmoothAt f x}}
  map := sorry

/-- The algebraic space underlying the smooth source locus of `f`. -/
def sourceLocusSpace {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    AlgebraicSpace S :=
  ofFunctor (sourceLocusSubfunctor f).toFunctor sorry sorry sorry

/-- The inclusion of the smooth source locus of `f` into `X`. -/
def sourceLocusι {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    sourceLocusSpace f ⟶ X :=
  (sourceLocusSubfunctor f).ι

/-- The inclusion of the smooth source locus is an open immersion. -/
instance instIsOpenImmersion_sourceLocusι {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : IsOpenImmersion (sourceLocusι f) :=
  sorry

namespace Smooth

/-- The largest open subspace of `X` on which `f` is smooth. -/
def sourceLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    OpenSubspace X :=
  OpenSubspace.ofι (sourceLocusι f)

/-- The inclusion of `sourceLocus f` is an open immersion. -/
instance instIsOpenImmersion_sourceLocus_ι {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : IsOpenImmersion (sourceLocus f).ι :=
  (sourceLocus f).isOpenImmersion

/-- The restriction of `f` to its smooth source locus is smooth. -/
instance instSmooth_sourceLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Smooth ((sourceLocus f).ι ≫ f) :=
  sorry

/-- A point of `X` lies in the smooth source locus of `f` if and only if `f` is
smooth at that point. -/
theorem mem_sourceLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) :
    x ∈ Set.range (Points.map (sourceLocus f).ι) ↔ SmoothAt f x :=
  sorry

/-- Any open immersion along which `f` is smooth factors through the smooth
source locus on points. -/
theorem sourceLocus_maximal {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {U : AlgebraicSpace S} (i : U ⟶ X) [IsOpenImmersion i]
    (hf : Smooth (i ≫ f)) :
    Set.range (Points.map i) ⊆ Set.range (Points.map (sourceLocus f).ι) :=
  sorry

/-- The smooth source locus is the open subspace cut out by the pointwise smooth
subfunctor, included by an open immersion along which `f` is smooth, whose
points are exactly the points at which `f` is smooth. -/
theorem sourceLocus_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (sourceLocusSpace f).functorOfPoints =
        (sourceLocusSubfunctor f).toFunctor ∧
      sourceLocusι f = (sourceLocusSubfunctor f).ι ∧
      IsOpenImmersion (sourceLocusι f) ∧
      Smooth ((sourceLocus f).ι ≫ f) ∧
      ∀ x : Points X,
        x ∈ Set.range (Points.map (sourceLocus f).ι) ↔ SmoothAt f x :=
  sorry

/-- In a cartesian square of algebraic spaces, pointwise smoothness is preserved
and reflected when the base morphism is flat and locally of finite presentation. -/
theorem smoothAt_iff_of_isPullback_of_flat_locallyOfFinitePresentation
    {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hcart : IsPullback g' f' f g) [Flat g] [LocallyOfFinitePresentation g]
    (x' : Points X') :
    SmoothAt f' x' ↔ SmoothAt f (Points.map g' x') :=
  sorry

/-- In a cartesian square of algebraic spaces over a flat base morphism,
pointwise smoothness is preserved and reflected when the original morphism is
locally of finite presentation. -/
theorem smoothAt_iff_of_isPullback_of_flat_base
    {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hcart : IsPullback g' f' f g) [LocallyOfFinitePresentation f] [Flat g]
    (x' : Points X') :
    SmoothAt f' x' ↔ SmoothAt f (Points.map g' x') :=
  sorry

end Smooth

end AlgebraicGeometry.AlgebraicSpace
