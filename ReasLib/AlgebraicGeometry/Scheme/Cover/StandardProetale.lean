module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import ReasLib.AlgebraicGeometry.Scheme.Cover.AffineFamily

/-!
# Standard pro-étale covering families

Finite affine weakly étale chart families are concrete data for refinements
and local computations, with direct bridges to the weakly étale and pro-étale
precoverages.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A finite family of affine weakly étale maps whose images cover an affine
target scheme. -/
@[stacks 098E]
structure StandardProetaleCover (T : Scheme.{u}) [IsAffine T] where
  /-- The number of charts. -/
  n : ℕ
  /-- The affine source schemes. -/
  U : Fin n → Scheme.{u}
  /-- The chart maps to the target. -/
  map : (j : Fin n) → U j ⟶ T
  /-- Each source chart is affine. -/
  isAffine : ∀ j, IsAffine (U j)
  /-- Each chart map is weakly étale. -/
  weaklyEtale : ∀ j, WeaklyEtale (map j)
  /-- The chart images jointly cover the target. -/
  cover : ∀ t : T, ∃ j, t ∈ Set.range (map j)

/-- Construct a standard pro-étale cover from a finite affine family whose
charts are weakly étale and whose images cover the target. -/
def StandardProetaleCover.ofAffineFamily {T : Scheme.{u}} [IsAffine T]
    (family : AffineFamilyOver T) (weaklyEtale : ∀ j, WeaklyEtale (family.map j))
    (cover : ∀ t : T, ∃ j, t ∈ Set.range (family.map j)) :
    StandardProetaleCover T where
  n := family.n
  U := family.U
  map := family.map
  isAffine := family.isAffine
  weaklyEtale := weaklyEtale
  cover := cover

/-- The chart maps of `ofAffineFamily` are the original affine-family maps. -/
@[simp]
theorem StandardProetaleCover.ofAffineFamily_map {T : Scheme.{u}} [IsAffine T]
    (family : AffineFamilyOver T) (weaklyEtale : ∀ j, WeaklyEtale (family.map j))
    (cover : ∀ t : T, ∃ j, t ∈ Set.range (family.map j)) (j : Fin family.n) :
    (StandardProetaleCover.ofAffineFamily family weaklyEtale cover).map j =
      family.map j := sorry

/-- The finite affine family underlying a standard pro-étale cover. -/
def StandardProetaleCover.toAffineFamily {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardProetaleCover T) : AffineFamilyOver T where
  n := 𝒰.n
  U := 𝒰.U
  map := 𝒰.map
  isAffine := 𝒰.isAffine

/-- The chart maps of `toAffineFamily` are the original chart maps. -/
@[simp]
theorem StandardProetaleCover.toAffineFamily_map {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardProetaleCover T) (j : Fin 𝒰.n) :
    𝒰.toAffineFamily.map j = 𝒰.map j := sorry

/-- The affine, weakly étale, and joint-cover conditions defining a standard
pro-étale cover. -/
theorem StandardProetaleCover.source_spec {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardProetaleCover T) :
    (∀ j, IsAffine (𝒰.U j)) ∧
      (∀ j, WeaklyEtale (𝒰.map j)) ∧
        (∀ t : T, ∃ j, t ∈ Set.range (𝒰.map j)) := sorry

/-- The finite chart family of a standard pro-étale cover as a canonical weakly
étale cover of the target. -/
def StandardProetaleCover.toWeaklyEtaleCover {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardProetaleCover T) :
    Scheme.Cover (Scheme.precoverage (@WeaklyEtale)) T :=
  Scheme.Cover.mkOfCovers (Fin 𝒰.n) 𝒰.U 𝒰.map 𝒰.cover 𝒰.weaklyEtale

/-- The schemes of `toWeaklyEtaleCover` are the original chart sources. -/
@[simp]
theorem StandardProetaleCover.toWeaklyEtaleCover_X {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardProetaleCover T) (j : Fin 𝒰.n) :
    𝒰.toWeaklyEtaleCover.X j = 𝒰.U j := sorry

/-- The maps of `toWeaklyEtaleCover` are the original chart maps. -/
@[simp]
theorem StandardProetaleCover.toWeaklyEtaleCover_f {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardProetaleCover T) (j : Fin 𝒰.n) :
    𝒰.toWeaklyEtaleCover.f j = 𝒰.map j := sorry

/-- The chart images of a standard pro-étale cover jointly cover the target. -/
theorem StandardProetaleCover.iUnion_range_eq_univ {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardProetaleCover T) :
    (⋃ j, Set.range (𝒰.map j)) = Set.univ := sorry

/-- A standard pro-étale cover generates a covering presieve for the weakly
étale precoverage. -/
theorem StandardProetaleCover.mem_weaklyEtale_precoverage {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardProetaleCover T) :
    Presieve.ofArrows 𝒰.U 𝒰.map ∈
      (Scheme.precoverage (@WeaklyEtale)).coverings T := sorry

/-- A standard pro-étale cover generates a covering presieve for the canonical
pro-étale precoverage. -/
theorem StandardProetaleCover.mem_proetale_precoverage {T : Scheme.{u}} [IsAffine T]
    (𝒰 : StandardProetaleCover T) :
    Presieve.ofArrows 𝒰.U 𝒰.map ∈ Scheme.proetalePrecoverage.coverings T := sorry

end AlgebraicGeometry
