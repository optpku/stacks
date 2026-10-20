/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Syntomic.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Standard

/-!
# Finite standard syntomic covers

This module provides finite affine standard syntomic covers and their
conversion to canonical syntomic covers.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A finite family of affine standard syntomic charts whose images cover an
affine target scheme. -/
@[stacks 0229]
structure StandardSyntomicCovering (T : Scheme.{u}) [IsAffine T] where
  /-- The number of charts. -/
  n : ℕ
  /-- The affine source schemes of the charts. -/
  U : Fin n → Scheme.{u}
  /-- The chart maps to the target. -/
  map : ∀ j, U j ⟶ T
  /-- Each source chart is affine. -/
  isAffine : ∀ j, IsAffine (U j)
  /-- Each global-sections map is a relative global complete intersection. -/
  isRelativeGlobalCompleteIntersection : ∀ j,
    let R := Scheme.Γ.obj (Opposite.op T)
    let A := Scheme.Γ.obj (Opposite.op (U j))
    let φ : R →+* A := CommRingCat.Hom.hom (Scheme.Hom.appTop (map j))
    let _ : Algebra R A := φ.toAlgebra
    Algebra.IsRelativeGlobalCompleteIntersection R A
  /-- The set-theoretic images of all charts cover the target. -/
  cover : ∀ t : T, ∃ j, t ∈ Set.range (map j)

/-- Construct a finite standard syntomic covering from explicit affine charts,
their coordinate-ring conditions, and their covering property. -/
def StandardSyntomicCovering.ofCharts
    {T : Scheme.{u}} [IsAffine T]
    (n : ℕ) (U : Fin n → Scheme.{u}) (map : ∀ j, U j ⟶ T)
    (isAffine : ∀ j, IsAffine (U j))
    (isRelativeGlobalCompleteIntersection : ∀ j,
      let R := Scheme.Γ.obj (Opposite.op T)
      let A := Scheme.Γ.obj (Opposite.op (U j))
      let φ : R →+* A := CommRingCat.Hom.hom (Scheme.Hom.appTop (map j))
      let _ : Algebra R A := φ.toAlgebra
      Algebra.IsRelativeGlobalCompleteIntersection R A)
    (cover : ∀ t : T, ∃ j, t ∈ Set.range (map j)) :
    StandardSyntomicCovering T where
  n := n
  U := U
  map := map
  isAffine := isAffine
  isRelativeGlobalCompleteIntersection := isRelativeGlobalCompleteIntersection
  cover := cover

/-- The property that a chart in a standard syntomic covering is standard
syntomic. -/
def StandardSyntomicCovering.IsStandardSyntomic
    {T : Scheme.{u}} [IsAffine T] (𝒰 : StandardSyntomicCovering T) (j : Fin 𝒰.n) : Prop :=
  -- Local instance justification (defeq pin): Standard syntomicity uses the chart's stored affineness.
  letI : IsAffine (𝒰.U j) := 𝒰.isAffine j
  StandardSyntomic (𝒰.map j)

/-- The defining affine, standard-syntomic, and covering data of a standard
syntomic cover. -/
theorem StandardSyntomicCovering.source_spec
    {T : Scheme.{u}} [IsAffine T] (𝒰 : StandardSyntomicCovering T) :
    (∀ j, IsAffine (𝒰.U j)) ∧
      (∀ j, 𝒰.IsStandardSyntomic j) ∧
        (∀ t : T, ∃ j, t ∈ Set.range (𝒰.map j)) := sorry

/-- Each chart map of a standard syntomic cover is standard syntomic. -/
theorem StandardSyntomicCovering.standardSyntomic
    {T : Scheme.{u}} [IsAffine T] (𝒰 : StandardSyntomicCovering T) (j : Fin 𝒰.n) :
    𝒰.IsStandardSyntomic j := sorry

/-- The global-sections map of a chart is a relative global complete
intersection. -/
theorem StandardSyntomicCovering.appTop_isRelativeGlobalCompleteIntersection
    {T : Scheme.{u}} [IsAffine T] (𝒰 : StandardSyntomicCovering T) (j : Fin 𝒰.n) :
    let R := Scheme.Γ.obj (Opposite.op T)
    let A := Scheme.Γ.obj (Opposite.op (𝒰.U j))
    let φ : R →+* A := CommRingCat.Hom.hom (Scheme.Hom.appTop (𝒰.map j))
    let _ : Algebra R A := φ.toAlgebra
    Algebra.IsRelativeGlobalCompleteIntersection R A := sorry

/-- Every chart map of a standard syntomic cover is syntomic. -/
theorem StandardSyntomicCovering.syntomic_map
    {T : Scheme.{u}} [IsAffine T] (𝒰 : StandardSyntomicCovering T) (j : Fin 𝒰.n) :
    Syntomic (𝒰.map j) := sorry

/-- The underlying finite standard syntomic family as a canonical syntomic
cover of its target. -/
def StandardSyntomicCovering.toSyntomicCover
    {T : Scheme.{u}} [IsAffine T] (𝒰 : StandardSyntomicCovering T) :
    SyntomicCover T :=
  Scheme.Cover.mkOfCovers (Fin 𝒰.n) 𝒰.U 𝒰.map 𝒰.cover 𝒰.syntomic_map

/-- The schemes of `toSyntomicCover` are the original source charts. -/
@[simp]
theorem StandardSyntomicCovering.toSyntomicCover_X
    {T : Scheme.{u}} [IsAffine T] (𝒰 : StandardSyntomicCovering T) (j : Fin 𝒰.n) :
    𝒰.toSyntomicCover.X j = 𝒰.U j := sorry

/-- The arrows of `toSyntomicCover` are the original chart maps. -/
@[simp]
theorem StandardSyntomicCovering.toSyntomicCover_f
    {T : Scheme.{u}} [IsAffine T] (𝒰 : StandardSyntomicCovering T) (j : Fin 𝒰.n) :
    𝒰.toSyntomicCover.f j = 𝒰.map j := sorry

end AlgebraicGeometry
