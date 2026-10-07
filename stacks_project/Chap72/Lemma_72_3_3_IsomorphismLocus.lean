module

public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage

/-!
# Isomorphism loci of morphisms of algebraic spaces

The maximal open of the target over which a morphism of algebraic spaces is an
isomorphism, recorded as a point-set of `|Y|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The inclusion of an open subspace is an open immersion. -/
instance OpenSubspace.instIsOpenImmersion {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : OpenSubspace X) : IsOpenImmersion U.ι :=
  U.isOpenImmersion

/-- The maximal open of the target over which a morphism of algebraic spaces is
an isomorphism, as the set of points of `|Y|` that lie in some open subspace
`U ⊂ Y` with `openInverseImageTo f U.ι` an isomorphism. -/
def isomorphismLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Set (Points Y) :=
  {y | ∃ U : OpenSubspace Y, y ∈ U.pointsSet ∧ IsIso (openInverseImageTo f U.ι)}

/-- A point of the target lies in the isomorphism locus if and only if it belongs
to an open subspace over which the comparison `openInverseImageTo f U.ι` is an
isomorphism. -/
theorem mem_isomorphismLocus_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {y : Points Y} :
    y ∈ isomorphismLocus f ↔
      ∃ U : OpenSubspace Y, y ∈ U.pointsSet ∧ IsIso (openInverseImageTo f U.ι) :=
  sorry

/-- Every open subspace of the target over which the morphism restricts to an
isomorphism is contained in the isomorphism locus. -/
theorem mem_isomorphismLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {U : OpenSubspace Y} (h : IsIso (openInverseImageTo f U.ι)) :
    U.pointsSet ⊆ isomorphismLocus f :=
  sorry

/-- The isomorphism locus is an open subset of `|Y|`, hence is the maximal open
of the target over which `f` is an isomorphism. -/
theorem isOpen_isomorphismLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : IsOpen (isomorphismLocus f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
