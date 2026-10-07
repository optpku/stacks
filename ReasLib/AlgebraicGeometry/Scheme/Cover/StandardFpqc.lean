module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc
public import ReasLib.AlgebraicGeometry.Scheme.Cover.StandardFpqc.Presentation

/-!
# Standard fpqc covering families

Finite affine flat chart families are explicit data for fpqc refinements.  The
module supplies direct computational projections to both the flat and fpqc
covering interfaces.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over

universe u

namespace AlgebraicGeometry

/-- The underlying finite chart family of a standard fpqc cover, viewed as a
canonical cover for the flat precoverage. -/
def StandardFpqcCover.toFlatCover {T : Scheme.{u}} (𝒰 : StandardFpqcCover T) :
    Scheme.Cover (Scheme.precoverage (fun {_ _} f ↦ Flat f)) T :=
  Scheme.Cover.mkOfCovers (Fin 𝒰.n) 𝒰.U 𝒰.map 𝒰.cover 𝒰.flat

/-- The schemes of `toFlatCover` are the original source charts. -/
@[simp]
theorem StandardFpqcCover.toFlatCover_X {T : Scheme.{u}}
    (𝒰 : StandardFpqcCover T) (j : Fin 𝒰.n) :
    𝒰.toFlatCover.X j = 𝒰.U j := sorry

/-- The maps of `toFlatCover` are the original chart maps. -/
@[simp]
theorem StandardFpqcCover.toFlatCover_f {T : Scheme.{u}}
    (𝒰 : StandardFpqcCover T) (j : Fin 𝒰.n) :
    𝒰.toFlatCover.f j = 𝒰.map j := sorry

/-- The fixed-target family underlying a standard fpqc cover. -/
abbrev StandardFpqcCover.toOverFamily {T : Scheme.{u}}
    (𝒰 : StandardFpqcCover T) : SemiRepresentableFamily.Over T :=
  ofArrows 𝒰.U 𝒰.map

/-- The `j`-th object of the fixed-target family is its chart map. -/
@[simp]
theorem StandardFpqcCover.toOverFamily_obj {T : Scheme.{u}}
    (𝒰 : StandardFpqcCover T) (j : Fin 𝒰.n) :
    𝒰.toOverFamily.obj j = Over.mk (𝒰.map j) := sorry

/-- The images of a standard fpqc cover's charts jointly cover its target. -/
theorem StandardFpqcCover.iUnion_range_eq_univ {T : Scheme.{u}}
    (𝒰 : StandardFpqcCover T) :
    (⋃ j, Set.range (𝒰.map j)) = Set.univ := sorry

/-- A standard fpqc cover generates a covering presieve for the flat
precoverage. -/
theorem StandardFpqcCover.mem_flat_precoverage {T : Scheme.{u}}
    (𝒰 : StandardFpqcCover T) :
    Presieve.ofArrows 𝒰.U 𝒰.map ∈
      (Scheme.precoverage (fun {_ _} f ↦ Flat f)).coverings T := sorry

/-- The canonical fpqc-covering predicate of the finite chart family. -/
theorem StandardFpqcCover.fpqcCovering {T : Scheme.{u}}
    (𝒰 : StandardFpqcCover T) :
    Scheme.FpqcCovering 𝒰.toOverFamily.obj := sorry

end AlgebraicGeometry
