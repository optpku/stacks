/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf

/-!
# Standard fppf covering families

Finite affine fppf chart families are explicit data for refinements and
computations, with bridges to the canonical fppf cover API.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A finite family of affine, flat, locally finitely presented maps whose
images cover an affine target scheme. -/
structure StandardFppfCover (T : Scheme.{u}) [IsAffine T] where
  /-- The number of charts. -/
  n : ℕ
  /-- The affine source schemes. -/
  U : Fin n → Scheme.{u}
  /-- The chart maps to the target. -/
  map : (j : Fin n) → U j ⟶ T
  /-- Each source scheme is affine. -/
  isAffine : ∀ j, IsAffine (U j)
  /-- Each chart map is flat. -/
  flat : ∀ j, Flat (map j)
  /-- Each chart map is locally of finite presentation. -/
  locallyOfFinitePresentation : ∀ j, LocallyOfFinitePresentation (map j)
  /-- The images of all chart maps cover the target. -/
  cover : ∀ t : T, ∃ j, t ∈ Set.range (map j)

/-- The defining affine, flat, finite-presentation, and cover conditions of a
standard fppf cover. -/
theorem StandardFppfCover.source_spec {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardFppfCover T) :
    (∀ j, IsAffine (𝒰.U j)) ∧
      (∀ j, Flat (𝒰.map j)) ∧
        (∀ j, LocallyOfFinitePresentation (𝒰.map j)) ∧
          (∀ t : T, ∃ j, t ∈ Set.range (𝒰.map j)) := sorry

/-- The canonical fppf cover associated to a finite standard fppf chart family. -/
def StandardFppfCover.toFppfCover {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardFppfCover T) : FppfCover T :=
  Scheme.Cover.mkOfCovers (Fin 𝒰.n) 𝒰.U 𝒰.map 𝒰.cover
    (fun j ↦ ⟨𝒰.flat j, 𝒰.locallyOfFinitePresentation j⟩)

/-- The schemes of `toFppfCover` are the original source charts. -/
@[simp]
theorem StandardFppfCover.toFppfCover_X {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardFppfCover T) (j : Fin 𝒰.n) :
    𝒰.toFppfCover.X j = 𝒰.U j := sorry

/-- The maps of `toFppfCover` are the original chart maps. -/
@[simp]
theorem StandardFppfCover.toFppfCover_f {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardFppfCover T) (j : Fin 𝒰.n) :
    𝒰.toFppfCover.f j = 𝒰.map j := sorry

/-- The images of the charts of a standard fppf cover jointly cover its target. -/
theorem StandardFppfCover.iUnion_range_eq_univ {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardFppfCover T) :
    (⋃ j, Set.range (𝒰.map j)) = Set.univ := sorry

/-- A standard fppf cover generates a covering presieve for the canonical fppf
precoverage. -/
theorem StandardFppfCover.mem_fppf_precoverage {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardFppfCover T) :
    Presieve.ofArrows 𝒰.U 𝒰.map ∈ Scheme.fppfPrecoverage.coverings T := sorry

/-- Forgetting local finite presentation, a standard fppf cover is a flat
covering family. -/
theorem StandardFppfCover.mem_flat_precoverage {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardFppfCover T) :
    Presieve.ofArrows 𝒰.U 𝒰.map ∈
      (Scheme.precoverage (fun {_ _} f ↦ Flat f)).coverings T := sorry

end AlgebraicGeometry
