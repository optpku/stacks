module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree.DegreeLocus
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap68.Definition_68_3_1_FiberDegree

/-!
# Degree-at-least loci of morphisms from schemes to algebraic spaces

This file owns the point-set of `|X|` on which the represented fibre of a
morphism `ofOver W ⟶ X` has degree at least `d`, together with the nested
open-subspace comparison API.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {W : Over S}

/-- The set of points of `X` at which the represented fibre of `f` has degree at
least `d`. -/
def degreeAtLeastLocus (f : ofOver W ⟶ X) (d : ℕ) : Set (Points X) :=
  {x | ∃ p : FieldValuedPoint X, Points.mk p = x ∧
    (fieldValuedPointPullbackSnd f p).HasDegreeAtLeast d}

/-- Membership in `degreeAtLeastLocus f d` means some field-valued representative
has fibre degree at least `d`. -/
theorem mem_degreeAtLeastLocus (f : ofOver W ⟶ X) (d : ℕ) (x : Points X) :
    x ∈ degreeAtLeastLocus f d ↔
      ∃ p : FieldValuedPoint X, Points.mk p = x ∧
        (fieldValuedPointPullbackSnd f p).HasDegreeAtLeast d :=
  sorry

/-- The represented fibre of `f` has degree at least `d` independently of the
choice of field-valued representative of a point of `X`. -/
theorem hasDegreeAtLeast_congr_mk (f : ofOver W ⟶ X) {p q : FieldValuedPoint X}
    (h : Points.mk p = Points.mk q) (d : ℕ) :
    (fieldValuedPointPullbackSnd f p).HasDegreeAtLeast d ↔
      (fieldValuedPointPullbackSnd f q).HasDegreeAtLeast d :=
  sorry

/-- A field-valued point of `X` lies in `degreeAtLeastLocus f d` if and only if
the represented fibre of `f` has degree at least `d`. -/
theorem mem_degreeAtLeastLocus_iff (f : ofOver W ⟶ X) (p : FieldValuedPoint X)
    (d : ℕ) :
    Points.mk p ∈ degreeAtLeastLocus f d ↔
      (fieldValuedPointPullbackSnd f p).HasDegreeAtLeast d :=
  sorry

/-- The degree-at-least-zero locus is all of `|X|`. -/
theorem degreeAtLeastLocus_zero (f : ofOver W ⟶ X) [Flat f]
    [LocallyOfFinitePresentation f] [Separated f] [LocallyQuasiFinite f] :
    degreeAtLeastLocus f 0 = Set.univ :=
  sorry

/-- The degree-at-least loci form a decreasing nested sequence. -/
theorem degreeAtLeastLocus_antitone (f : ofOver W ⟶ X) [Flat f]
    [LocallyOfFinitePresentation f] [Separated f] [LocallyQuasiFinite f] :
    Antitone (degreeAtLeastLocus f) :=
  sorry

/-- For a flat, locally finitely presented, separated, locally quasi-finite
morphism, the degree-at-least locus is open. -/
theorem degreeAtLeastLocus_isOpen (f : ofOver W ⟶ X) [Flat f]
    [LocallyOfFinitePresentation f] [Separated f] [LocallyQuasiFinite f]
    (d : ℕ) :
    IsOpen (degreeAtLeastLocus f d) :=
  sorry

/-- There is an open subspace of `X` whose underlying point-set is the
degree-at-least locus. -/
theorem exists_degreeAtLeastOpen (f : ofOver W ⟶ X) [Flat f]
    [LocallyOfFinitePresentation f] [Separated f] [LocallyQuasiFinite f]
    (d : ℕ) :
    ∃ U : OpenSubspace X, U.pointsSet = degreeAtLeastLocus f d :=
  sorry

/-- A field-valued point factors through an open subspace with point-set
`degreeAtLeastLocus f d` if and only if the represented fibre has degree at
least `d`. -/
theorem factorsThrough_degreeAtLeastLocus_iff (f : ofOver W ⟶ X) [Flat f]
    [LocallyOfFinitePresentation f] [Separated f] [LocallyQuasiFinite f]
    (p : FieldValuedPoint X) (d : ℕ) {U : OpenSubspace X}
    (hU : U.pointsSet = degreeAtLeastLocus f d) :
    (∃ lift : ofOver p.overObj ⟶ U.X, lift ≫ U.ι = p.hom) ↔
      (fieldValuedPointPullbackSnd f p).HasDegreeAtLeast d :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
