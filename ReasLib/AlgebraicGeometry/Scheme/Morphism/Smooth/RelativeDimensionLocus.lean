/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Differentials
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The locus where a smooth morphism has a prescribed finite fiber dimension is clopen. -/
theorem smoothRelativeDimensionLocus_isClopen {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Smooth f] (t : ℕ) :
    IsClopen {x : X | f.fiberDimensionAt x = (t : WithBot ℕ∞)} := sorry

/-- The open locus where a smooth morphism has fiber dimension `t`. -/
def smoothRelativeDimensionLocus {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Smooth f] (t : ℕ) : X.Opens :=
  ⟨{x : X | f.fiberDimensionAt x = (t : WithBot ℕ∞)},
    (smoothRelativeDimensionLocus_isClopen f t).isOpen⟩

/-- Membership in a smooth relative-dimension locus is the corresponding fiber-dimension
equality. -/
theorem mem_smoothRelativeDimensionLocus {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Smooth f] (t : ℕ) (x : X) :
    x ∈ smoothRelativeDimensionLocus f t ↔
      f.fiberDimensionAt x = (t : WithBot ℕ∞) := Iff.rfl

/-- The finite relative-dimension loci of a smooth morphism cover its source. -/
theorem smoothRelativeDimensionLocus_iSup {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Smooth f] :
    iSup (smoothRelativeDimensionLocus f) = ⊤ := sorry

/-- Distinct relative-dimension loci of a smooth morphism are disjoint. -/
theorem smoothRelativeDimensionLocus_pairwiseDisjoint {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Smooth f] :
    Pairwise (fun t s : ℕ ↦ Disjoint
      (smoothRelativeDimensionLocus f t : Set X)
      (smoothRelativeDimensionLocus f s : Set X)) := sorry

/-- Restriction to the fiber-dimension-`t` locus has constant relative dimension `t`. -/
@[instance]
theorem relativeDimension_smoothRelativeDimensionLocus {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Smooth f] (t : ℕ) :
    RelativeDimension
      (f.resLE ⊤ (smoothRelativeDimensionLocus f t) (by simp)) t := sorry

end AlgebraicGeometry.Scheme.Hom
