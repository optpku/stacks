/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import ReasLib.CategoryTheory.Sites.Family

/-!
# Standard étale covering families

Finite affine étale chart families are concrete data for refinements and local
computations, with direct bridges to the canonical étale precoverage.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over

universe u

namespace AlgebraicGeometry

/-- A finite family of affine étale maps whose images cover an affine target scheme. -/
structure StandardEtaleCover (T : Scheme.{u}) [IsAffine T] where
  /-- The number of charts. -/
  n : ℕ
  /-- The affine source schemes. -/
  U : Fin n → Scheme.{u}
  /-- The chart maps to the target. -/
  map : (j : Fin n) → U j ⟶ T
  /-- Each source chart is affine. -/
  isAffine : ∀ j, IsAffine (U j)
  /-- Each chart map is étale. -/
  etale : ∀ j, Etale (map j)
  /-- The chart images jointly cover the target. -/
  cover : ∀ t : T, ∃ j, t ∈ Set.range (map j)

/-- The affine, étale, and joint-cover conditions defining a standard étale
cover. -/
theorem StandardEtaleCover.source_spec {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardEtaleCover T) :
    (∀ j, IsAffine (𝒰.U j)) ∧
      (∀ j, Etale (𝒰.map j)) ∧
        (∀ t : T, ∃ j, t ∈ Set.range (𝒰.map j)) := sorry

/-- The finite chart family of a standard étale cover as a canonical étale
cover of the target. -/
def StandardEtaleCover.toEtaleCovering {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardEtaleCover T) : Scheme.Cover Scheme.etalePrecoverage T :=
  Scheme.Cover.mkOfCovers (Fin 𝒰.n) 𝒰.U 𝒰.map 𝒰.cover 𝒰.etale

/-- The schemes of `toEtaleCovering` are the original chart sources. -/
@[simp] theorem StandardEtaleCover.toEtaleCovering_X {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardEtaleCover T) (j : Fin 𝒰.n) :
    𝒰.toEtaleCovering.X j = 𝒰.U j := sorry

/-- The maps of `toEtaleCovering` are the original chart maps. -/
@[simp] theorem StandardEtaleCover.toEtaleCovering_f {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardEtaleCover T) (j : Fin 𝒰.n) :
    𝒰.toEtaleCovering.f j = 𝒰.map j := sorry

/-- The fixed-target family underlying a standard étale cover. -/
abbrev StandardEtaleCover.toOverFamily {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardEtaleCover T) : SemiRepresentableFamily.Over T :=
  ofArrows 𝒰.U 𝒰.map

/-- The `j`-th object of the fixed-target family is its chart map. -/
@[simp] theorem StandardEtaleCover.toOverFamily_obj {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardEtaleCover T) (j : Fin 𝒰.n) :
    𝒰.toOverFamily.obj j = Over.mk (𝒰.map j) := sorry

/-- The chart images of a standard étale cover jointly cover the target. -/
theorem StandardEtaleCover.iUnion_range_eq_univ {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardEtaleCover T) :
    (⋃ j, Set.range (𝒰.map j)) = Set.univ := sorry

/-- A standard étale cover generates a covering presieve for the canonical
étale precoverage. -/
theorem StandardEtaleCover.mem_etale_precoverage {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardEtaleCover T) :
    Presieve.ofArrows 𝒰.U 𝒰.map ∈ Scheme.etalePrecoverage.coverings T := sorry

end AlgebraicGeometry
