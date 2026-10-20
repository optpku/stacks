/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree.DegreeLocus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiberDegree
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat

/-!
# Degree-at-least loci of morphisms from schemes to algebraic spaces

The points where a represented fibre has degree at least a given natural number
form a decreasing sequence of loci. For flat, locally finitely presented,
separated, locally quasi-finite morphisms these loci define open subspaces.
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
  Iff.rfl

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

/-- The open subspaces where the represented fibres have degree at least `d`,
with the identity open subspace as the zero stage. -/
def degreeAtLeastOpen (f : ofOver W ⟶ X) [Flat f]
    [LocallyOfFinitePresentation f] [Separated f] [LocallyQuasiFinite f] :
    ℕ → OpenSubspace X := fun d ↦
  match d with
  | Nat.zero => OpenSubspace.id X
  | Nat.succ n => OpenSubspace.fromOpens
      ⟨degreeAtLeastLocus f (n + 1), degreeAtLeastLocus_isOpen f (n + 1)⟩

/-- The underlying points of each degree open subspace are precisely the
corresponding degree-at-least locus. -/
theorem degreeAtLeastOpen_pointsSet (f : ofOver W ⟶ X) [Flat f]
    [LocallyOfFinitePresentation f] [Separated f] [LocallyQuasiFinite f]
    (d : ℕ) :
    (degreeAtLeastOpen f d).pointsSet = degreeAtLeastLocus f d := by
  cases d with
  | zero =>
      exact (OpenSubspace.pointsSet_id X).trans (degreeAtLeastLocus_zero f).symm
  | succ n =>
      exact OpenSubspace.fromOpens_pointsSet
        ⟨degreeAtLeastLocus f (n + 1), degreeAtLeastLocus_isOpen f (n + 1)⟩

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

/-- A flat, locally finitely presented, separated, locally quasi-finite morphism
admits a decreasing sequence of open subspaces starting at the whole target,
through whose degree `d` stage a field-valued point factors exactly when its
represented fibre has degree at least `d`. -/
theorem exists_degreeAtLeastOpen (f : ofOver W ⟶ X) [Flat f]
    [LocallyOfFinitePresentation f] [Separated f] [LocallyQuasiFinite f] :
    ∃ U : ℕ → OpenSubspace X,
      U 0 = OpenSubspace.id X ∧
      Antitone (fun d ↦ (U d).pointsSet) ∧
      ∀ (p : FieldValuedPoint X) (d : ℕ),
        ((∃ lift : ofOver p.overObj ⟶ (U d).X, lift ≫ (U d).ι = p.hom) ↔
          (fieldValuedPointPullbackSnd f p).HasDegreeAtLeast d) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
