/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AffinePresentation
public import ReasLib.AlgebraicGeometry.FormalSpectrum.Colimit
public import ReasLib.RingTheory.Topology.Adic.Weakly

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- An affine formal algebraic space is weakly adic when it has the weak-ideal
quotient presentation of a weakly adic, weakly admissible ring. -/
@[mk_iff]
class IsWeaklyAdic {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) : Prop
    extends IsAffine X where
  /-- A weakly adic ring presents the space by its actual weak-ideal thickenings. -/
  exists_weaklyAdic :
    ∃ (B : Type u) (_ : CommRing B) (_ : TopologicalSpace B)
      (_ : TopologicalRing.IsWeaklyAdicRing B)
      (_ : TopologicalRing.IsWeaklyAdmissibleRing B)
      (σ : Spec (.of B) ⟶ S),
      FormalAlgebraicSpace.IsDirectedAffineThickeningColimit (thickenings B σ) X

namespace IsWeaklyAdic

/-- The sheaf formal spectrum of a weakly adic, weakly admissible ring is weakly adic. -/
instance instSpf (B : Type u) [CommRing B] [TopologicalSpace B]
    [TopologicalRing.IsWeaklyAdicRing B] [TopologicalRing.IsWeaklyAdmissibleRing B]
    {S : Scheme.{u}} (σ : Spec (.of B) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)] :
    IsWeaklyAdic (spf B σ).obj :=
  sorry

/-- A weakly adic affine formal algebraic space has a compatible weak-ideal
quotient presentation by a weakly adic, weakly admissible ring. -/
theorem spec {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) [IsWeaklyAdic X] :
    ∃ (B : Type u) (_ : CommRing B) (_ : TopologicalSpace B)
      (_ : TopologicalRing.IsWeaklyAdicRing B)
      (_ : TopologicalRing.IsWeaklyAdmissibleRing B)
      (σ : Spec (.of B) ⟶ S),
      FormalAlgebraicSpace.IsDirectedAffineThickeningColimit (thickenings B σ) X :=
  sorry

/-- Weak adicity is equivalent to canonical affineness and a compatible
weak-ideal quotient presentation by a weakly adic, weakly admissible ring. -/
theorem iff {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) :
    IsWeaklyAdic X ↔ IsAffine X ∧
      ∃ (B : Type u) (_ : CommRing B) (_ : TopologicalSpace B)
        (_ : TopologicalRing.IsWeaklyAdicRing B)
        (_ : TopologicalRing.IsWeaklyAdmissibleRing B)
        (σ : Spec (.of B) ⟶ S),
        FormalAlgebraicSpace.IsDirectedAffineThickeningColimit (thickenings B σ) X :=
  sorry

end IsWeaklyAdic

end AlgebraicGeometry.AffineFormalAlgebraicSpace
