/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.AffineFamily
public import ReasLib.AlgebraicGeometry.Scheme.Cover.StandardSyntomic.Basic

/-!
# Standard syntomic covering families

Finite affine standard syntomic charts are retained as concrete data so that
refinement and pointwise applications do not have to unpack a generic cover.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- The finite affine family underlying a standard syntomic covering. -/
def StandardSyntomicCovering.toAffineFamily
    {T : Scheme.{u}} [IsAffine T] (𝒰 : StandardSyntomicCovering T) :
    AffineFamilyOver T where
  n := 𝒰.n
  U := 𝒰.U
  map := 𝒰.map
  isAffine := 𝒰.isAffine

/-- The `j`-th chart map of the affine family underlying a standard syntomic
covering is its original chart map. -/
@[simp]
theorem StandardSyntomicCovering.toAffineFamily_map
    {T : Scheme.{u}} [IsAffine T] (𝒰 : StandardSyntomicCovering T) (j : Fin 𝒰.n) :
    𝒰.toAffineFamily.map j = 𝒰.map j := sorry

/-- The images of the charts of a standard syntomic cover jointly cover its
target. -/
theorem StandardSyntomicCovering.iUnion_range_eq_univ
    {T : Scheme.{u}} [IsAffine T] (𝒰 : StandardSyntomicCovering T) :
    (⋃ j, Set.range (𝒰.map j)) = Set.univ := sorry

/-- A standard syntomic cover generates a covering presieve in the canonical
syntomic precoverage. -/
theorem StandardSyntomicCovering.mem_syntomic_precoverage
    {T : Scheme.{u}} [IsAffine T] (𝒰 : StandardSyntomicCovering T) :
    Presieve.ofArrows 𝒰.U 𝒰.map ∈ (Scheme.precoverage (@Syntomic)).coverings T := sorry

end AlgebraicGeometry
