/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.MorphismProperty
public import stacks_project.Chap67.Remark_67_12_5_Opens
public import stacks_project.Chap74.Lemma_74_7_1_InverseImage
public import stacks_project.Chap74.Lemma_74_10_2_BaseChange

/-!
# Target locus of a morphism property of algebraic spaces

The largest open subspace of the target of a morphism of algebraic spaces on
which a given morphism property holds, constructed from the union of good
open point-sets.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The predicate that a precoverage is one of the fppf, syntomic, smooth, or
étale precoverages on algebraic spaces over `S`. -/
def isFppfToEtalePrecoverage {S : Scheme.{u}} (K : Precoverage (AlgebraicSpace S)) :
    Prop :=
  K = fppfPrecoverage S ∨ K = syntomicPrecoverage S ∨
    K = smoothPrecoverage S ∨ K = @etalePrecoverage S

/-- `isFppfToEtalePrecoverage K` holds exactly for the fppf, syntomic, smooth, or
étale precoverage. -/
theorem isFppfToEtalePrecoverage_iff {S : Scheme.{u}}
    {K : Precoverage (AlgebraicSpace S)} :
    isFppfToEtalePrecoverage K ↔
      K = fppfPrecoverage S ∨ K = syntomicPrecoverage S ∨
        K = smoothPrecoverage S ∨ K = @etalePrecoverage S :=
  sorry

/-- A morphism of algebraic spaces which is flat and locally of finite
presentation, syntomic, smooth, or étale. -/
def isFppfToEtale {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  (Flat f ∧ LocallyOfFinitePresentation f) ∨ Syntomic f ∨ Smooth f ∨ Etale f

/-- `isFppfToEtale f` holds exactly when `f` is flat and locally of finite
presentation, syntomic, smooth, or étale. -/
theorem isFppfToEtale_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    isFppfToEtale f ↔
      (Flat f ∧ LocallyOfFinitePresentation f) ∨ Syntomic f ∨ Smooth f ∨ Etale f :=
  sorry

/-- The underlying points of the target locus of `P` at `f`, namely the union of
point-sets of open subspaces of `Y` along which the restriction of `f` has `P`. -/
def targetLocusPoints {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Set (Points Y) :=
  {y | ∃ U : OpenSubspace Y, y ∈ U.pointsSet ∧ P (pullback.snd f U.ι)}

/-- A point of `Y` lies in `targetLocusPoints P f` if and only if it lies in some
open subspace of `Y` along which the restriction of `f` has `P`. -/
theorem mem_targetLocusPoints {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {y : Points Y} :
    y ∈ targetLocusPoints P f ↔
      ∃ U : OpenSubspace Y, y ∈ U.pointsSet ∧ P (pullback.snd f U.ι) :=
  sorry

/-- `targetLocusPoints P f` is open in `|Y|`. -/
theorem isOpen_targetLocusPoints {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : IsOpen (targetLocusPoints P f) :=
  sorry

/-- The largest open subspace of `Y` along which the restriction of `f` has `P`. -/
def targetLocus {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) : OpenSubspace Y :=
  OpenSubspace.ofOpens ⟨targetLocusPoints P f, isOpen_targetLocusPoints P f⟩

/-- The underlying point-set of `targetLocus P f` is `targetLocusPoints P f`. -/
theorem targetLocus_pointsSet {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : (targetLocus P f).pointsSet = targetLocusPoints P f :=
  sorry

/-- A point of `Y` lies in `targetLocus P f` if and only if it lies in some open
subspace of `Y` along which the restriction of `f` has `P`. -/
theorem mem_targetLocus {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) {y : Points Y} :
    y ∈ (targetLocus P f).pointsSet ↔
      ∃ U : OpenSubspace Y, y ∈ U.pointsSet ∧ P (pullback.snd f U.ι) :=
  sorry

/-- Every open subspace of `Y` along which the restriction of `f` has `P` factors
through `targetLocus P f`. -/
theorem targetLocus_maximal {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (V : OpenSubspace Y) (hV : P (pullback.snd f V.ι)) :
    ∃ χ : V.X ⟶ (targetLocus P f).X, χ ≫ (targetLocus P f).ι = V.ι :=
  sorry

/-- `targetLocus P f` occupies `targetLocusPoints P f`, and is unique up to unique
lift over `Y`. -/
theorem targetLocus_spec {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (targetLocus P f).pointsSet = targetLocusPoints P f ∧
      ∀ V : OpenSubspace Y, V.pointsSet = targetLocusPoints P f →
        ∃! χ : V.X ⟶ (targetLocus P f).X, χ ≫ (targetLocus P f).ι = V.ι :=
  sorry

/-- The target locus of a base change along `g` has the same point-set as the
inverse image of `targetLocus P f` along `g`. -/
theorem targetLocus_inverseImage_eq {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    {K : Precoverage (AlgebraicSpace S)} [P.IsLocalAtTarget K]
    (hτ : isFppfToEtalePrecoverage K) {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hg : isFppfToEtale g) :
    (targetLocus P (pullback.snd f g)).pointsSet =
      ((targetLocus P f).inverseImage g).pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
