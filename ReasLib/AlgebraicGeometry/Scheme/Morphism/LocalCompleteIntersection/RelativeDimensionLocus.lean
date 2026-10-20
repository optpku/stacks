/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.FiberDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.LocalCompleteIntersection

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The finite fiber-dimension loci of a flat local complete intersection morphism are
clopen. -/
theorem flatLciDimensionLocus_isClopen {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [LocallyOfType RingHom.IsLocalCompleteIntersection f] (r : ℕ) :
    IsClopen {x : X | f.fiberDimensionAt x = (r : WithBot ℕ∞)} := sorry

/-- The locus on which a flat local complete intersection morphism has fiber dimension `r`.
These loci allow flat pullback to have different degrees on different components. -/
def flatLciDimensionLocus {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [LocallyOfType RingHom.IsLocalCompleteIntersection f] (r : ℕ) : X.Opens :=
  ⟨{x : X | f.fiberDimensionAt x = (r : WithBot ℕ∞)},
    (flatLciDimensionLocus_isClopen f r).isOpen⟩

/-- Membership in a flat lci dimension locus is the indicated fiber-dimension equality. -/
theorem mem_flatLciDimensionLocus {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [LocallyOfType RingHom.IsLocalCompleteIntersection f] (r : ℕ) (x : X) :
    x ∈ flatLciDimensionLocus f r ↔
      f.fiberDimensionAt x = (r : WithBot ℕ∞) := Iff.rfl

/-- The constant finite fiber-dimension loci cover a flat lci morphism's source. -/
theorem flatLciDimensionLocus_iSup {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [LocallyOfType RingHom.IsLocalCompleteIntersection f] :
    iSup (flatLciDimensionLocus f) = ⊤ := sorry

/-- Different fiber-dimension loci of a flat lci morphism are disjoint. -/
theorem flatLciDimensionLocus_pairwiseDisjoint {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [LocallyOfType RingHom.IsLocalCompleteIntersection f] :
    Pairwise (fun r s : ℕ ↦ Disjoint
      (flatLciDimensionLocus f r : Set X) (flatLciDimensionLocus f s : Set X)) := sorry

/-- The restriction of a flat lci morphism to its dimension-`r` locus has relative
dimension `r`; no global relative-dimension assumption is needed. -/
@[instance]
theorem relativeDimension_flatLciDimensionLocus {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [LocallyOfType RingHom.IsLocalCompleteIntersection f] (r : ℕ) :
    RelativeDimension (f.resLE ⊤ (flatLciDimensionLocus f r) (by simp)) r := sorry

end AlgebraicGeometry.Scheme.Hom
