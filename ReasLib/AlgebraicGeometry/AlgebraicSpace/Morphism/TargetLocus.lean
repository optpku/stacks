/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.MorphismProperty
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalAtTarget.BaseChange

/-!
# Target loci of morphism properties of algebraic spaces

The union of good target opens defines a candidate locus for any morphism property.
For a property local on the target in the fppf, syntomic, smooth, or étale topology,
this locus is good and commutes with base changes admitted by that topology.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- The predicate that a precoverage is one of the fppf, syntomic, smooth, or
étale precoverages on algebraic spaces over `S`. -/
def isFppfToEtalePrecoverage {S : Scheme.{u}} (K : Precoverage (AlgebraicSpace S)) :
    Prop :=
  K = fppfPrecoverage S ∨ K = syntomicPrecoverage S ∨
    K = smoothPrecoverage S ∨ K = etalePrecoverage

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

/-- The candidate target locus obtained from the union of good open subspaces.
Its restriction has `P` when `P` is local on the target for one of the fppf,
syntomic, smooth, or étale precoverages. -/
def targetLocus {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) : OpenSubspace Y :=
  OpenSubspace.fromOpens ⟨targetLocusPoints P f, isOpen_targetLocusPoints P f⟩

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

/-- For a property local on the target in the fppf, syntomic, smooth, or étale
topology, the target locus has the property and every good open subspace factors
through its inclusion. -/
theorem targetLocus_isLargest {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    {K : Precoverage (AlgebraicSpace S)} [P.IsLocalAtTarget K]
    (hτ : isFppfToEtalePrecoverage K) {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    P (pullback.snd f (targetLocus P f).ι) ∧
      ∀ V : OpenSubspace Y, P (pullback.snd f V.ι) →
        ∃ χ : V.X ⟶ (targetLocus P f).X, χ ≫ (targetLocus P f).ι = V.ι :=
  sorry

/-- A morphism occurring in a covering for the selected fppf, syntomic, smooth,
or étale precoverage factors through the target locus whenever the base change
has the target-local property. -/
theorem factorsThrough_targetLocus {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    {K : Precoverage (AlgebraicSpace S)} [P.IsLocalAtTarget K]
    (hτ : isFppfToEtalePrecoverage K) {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hg : K.morphismProperty g)
    (hf : P (pullback.snd f g)) :
    ∃ χ : Y' ⟶ (targetLocus P f).X, χ ≫ (targetLocus P f).ι = g :=
  sorry

/-- The target locus of a target-local property commutes, on underlying point
sets, with base change by a morphism occurring in a covering for the selected
fppf, syntomic, smooth, or étale precoverage. -/
theorem targetLocus_inverseImage {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    {K : Precoverage (AlgebraicSpace S)} [P.IsLocalAtTarget K]
    (hτ : isFppfToEtalePrecoverage K) {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hg : K.morphismProperty g) :
    (targetLocus P (pullback.snd f g)).pointsSet =
      Points.map g ⁻¹' (targetLocus P f).pointsSet :=
  sorry

/-- For a property local on the target in the selected fppf, syntomic, smooth,
or étale topology, its target locus pulls back to the target locus along every
member of a covering family with an arbitrary index universe. -/
theorem targetLocus_inverseImage_cover {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    {K : Precoverage (AlgebraicSpace S)} [P.IsLocalAtTarget K]
    (hτ : isFppfToEtalePrecoverage K) {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (𝒰 : Precoverage.ZeroHypercover.{v} K Y) (i : 𝒰.I₀) :
    (targetLocus P (pullback.snd f (𝒰.f i))).pointsSet =
      Points.map (𝒰.f i) ⁻¹' (targetLocus P f).pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
