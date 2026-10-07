module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap76.Definition_76_48_1_LocalCompleteIntersection

/-!
# Koszul locus of a morphism of algebraic spaces

The open subspace `U(f) ⊂ X` consisting of the points at which a morphism
`f : X ⟶ Y` of algebraic spaces is Koszul.

The `OpenSubspace.ofOpens` owner currently rebuilds the broken
`Chap66.Lemma_66_4_2_Comparison`. This module constructs `U(f)` as the
subfunctor of maps into `X` whose image of points lands in the Koszul set,
matching `Unramified.sourceLocus`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The morphism `ofOver U.unop ⟶ X` associated to a section of the functor of
points. -/
def homOfPointsSection {S : Scheme.{u}} {X : AlgebraicSpace S} {U : (Over S)ᵒᵖ}
    (φ : X.functorOfPoints.obj U) : ofOver U.unop ⟶ X :=
  yonedaEquiv.symm φ

/-- `homOfPointsSection φ` is the Yoneda transpose of a section of the functor of
points. -/
theorem homOfPointsSection_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : (Over S)ᵒᵖ} (φ : X.functorOfPoints.obj U) :
    homOfPointsSection φ = yonedaEquiv.symm φ :=
  sorry

namespace OpenSubspace

/-- The underlying set of points of an open subspace, as the image of `|U| → |X|`. -/
def pointsSet {S : Scheme.{u}} {X : AlgebraicSpace S} (U : OpenSubspace X) :
    Set (Points X) :=
  Set.range (Points.map U.ι)

/-- `pointsSet U` is the range of `Points.map U.ι`. -/
theorem pointsSet_eq {S : Scheme.{u}} {X : AlgebraicSpace S} (U : OpenSubspace X) :
    U.pointsSet = Set.range (Points.map U.ι) :=
  sorry

end OpenSubspace

/-- The set of points of `X` at which `f` is Koszul. -/
def koszulLocusPointsSet {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Set (Points X) :=
  {x | KoszulAt f x}

/-- The subfunctor of maps into `X` whose image of points lands in the Koszul
locus of `f`. -/
def koszulLocusSubfunctor {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Subfunctor X.functorOfPoints where
  obj U := {φ | Set.range (Points.map (homOfPointsSection φ)) ⊆ koszulLocusPointsSet f}
  map := sorry

/-- The algebraic space underlying the Koszul locus of `f`. -/
def koszulLocusSpace {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    AlgebraicSpace S :=
  ofFunctor (koszulLocusSubfunctor f).toFunctor sorry sorry sorry

/-- The inclusion of the Koszul locus of `f` into `X`. -/
def koszulLocusι {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    koszulLocusSpace f ⟶ X :=
  (koszulLocusSubfunctor f).ι

/-- The functor of points of `koszulLocusSpace f` is the Koszul-locus subfunctor. -/
theorem koszulLocusSpace_functorOfPoints {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    (koszulLocusSpace f).functorOfPoints = (koszulLocusSubfunctor f).toFunctor :=
  sorry

/-- The inclusion `koszulLocusι f` is the subfunctor inclusion. -/
theorem koszulLocusι_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    koszulLocusι f = (koszulLocusSubfunctor f).ι :=
  sorry

/-- The inclusion of the Koszul locus is an open immersion. -/
instance instIsOpenImmersion_koszulLocusι {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) : IsOpenImmersion (koszulLocusι f) :=
  sorry

/-- The open subspace `U(f) ⊂ X` whose points are those at which `f` is Koszul. -/
def koszulLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : OpenSubspace X :=
  OpenSubspace.ofι (koszulLocusι f)

/-- The underlying point-set of `koszulLocus f` is `koszulLocusPointsSet f`. -/
theorem koszulLocus_pointsSet_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : (koszulLocus f).pointsSet = koszulLocusPointsSet f :=
  sorry

/-- A point of `X` lies in the Koszul locus of `f` if and only if `f` is Koszul
at that point. -/
theorem mem_koszulLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) :
    x ∈ (koszulLocus f).pointsSet ↔ KoszulAt f x :=
  sorry

/-- The Koszul locus occupies the set of Koszul points, uniquely up to unique
lift over `X`. -/
theorem koszulLocus_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    (koszulLocus f).pointsSet = {x | KoszulAt f x} ∧
      ∀ V : OpenSubspace X, V.pointsSet = {x | KoszulAt f x} →
        ∃! φ : V.X ⟶ (koszulLocus f).X, φ ≫ (koszulLocus f).ι = V.ι :=
  sorry

/-- The inclusion of the Koszul locus is an open immersion. -/
instance instIsOpenImmersion_koszulLocus_ι {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    IsOpenImmersion (koszulLocus f).ι :=
  (koszulLocus f).isOpenImmersion

end AlgebraicGeometry.AlgebraicSpace
