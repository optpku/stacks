/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import ReasLib.AlgebraicGeometry.Scheme.Cover.AffineFamily

/-!
# Standard fpqc cover presentations

This module owns finite affine flat chart presentations whose images jointly
cover an affine target, together with their underlying affine families.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A finite family of affine flat maps whose images cover an affine target
scheme. -/
@[stacks 022F]
structure StandardFpqcCover (T : Scheme.{u}) where
  /-- The target scheme is affine. -/
  isAffineTarget : IsAffine T
  /-- The number of charts. -/
  n : ℕ
  /-- The affine source schemes. -/
  U : Fin n → Scheme.{u}
  /-- The chart maps to the target. -/
  map : (j : Fin n) → U j ⟶ T
  /-- Each source chart is affine. -/
  isAffine : ∀ j, IsAffine (U j)
  /-- Each chart map is flat. -/
  flat : ∀ j, Flat (map j)
  /-- The images of the charts jointly cover the target. -/
  cover : ∀ t : T, ∃ j, t ∈ Set.range (map j)

/-- The defining target-affine, source-affine, flat, and joint-cover conditions
of a standard fpqc cover. -/
theorem StandardFpqcCover.source_spec {T : Scheme.{u}} (𝒰 : StandardFpqcCover T) :
    IsAffine T ∧
      (∀ j, IsAffine (𝒰.U j)) ∧
        (∀ j, Flat (𝒰.map j)) ∧
          (∀ t : T, ∃ j, t ∈ Set.range (𝒰.map j)) := sorry

namespace StandardFpqcCover

variable {T : Scheme.{u}}

/-- The finite affine family underlying a standard fpqc cover. -/
def toAffineFamily (cover : StandardFpqcCover T) : AffineFamilyOver T where
  n := cover.n
  U := cover.U
  map := cover.map
  isAffine := cover.isAffine

/-- The chart maps of `toAffineFamily` are the original fpqc chart maps. -/
@[simp] theorem toAffineFamily_map (cover : StandardFpqcCover T)
    (j : Fin cover.n) :
    (toAffineFamily cover).map j = cover.map j := sorry

end StandardFpqcCover

end AlgebraicGeometry
