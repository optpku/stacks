module

public import Mathlib.RingTheory.FiniteType
public import ReasLib.RingTheory.Topology.WeaklyAdmissible
public import ReasLib.RingTheory.Topology.TopologicalNilradical.Quotient
public import ReasLib.RingTheory.Topology.LocalMorphismProperty

/-!
# Finite type on reductions of weakly admissible rings

A homomorphism of weakly admissible rings is of finite type on reduction when
the induced map on quotients by topological nilradicals is of finite type.
This property is local on countably indexed weakly admissible rings.
-/

@[expose] public section

universe u

open TopologicalRing

namespace RingHom

variable {A B : Type u} [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A]
  [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B]

/-- The homomorphism `φ : A →+* B` of weakly admissible rings is of finite type
on reduction when the induced map
`A ⧸ topologicalNilradical A →+* B ⧸ topologicalNilradical B` is of finite
type. -/
def IsFiniteTypeOnReduction (φ : A →+* B) : Prop :=
  ∃ h : topologicalNilradical A ≤ (topologicalNilradical B).comap φ,
    (Ideal.quotientMap (topologicalNilradical B) φ h).FiniteType

/-- For a continuous homomorphism of weakly admissible rings, finite type on
reduction is equivalent to finite type of the induced map on topological
nilradical quotients. -/
theorem isFiniteTypeOnReduction_iff (φ : A →+* B) (hφ : Continuous φ) :
    φ.IsFiniteTypeOnReduction ↔ (topologicalNilradical.quotientMap φ hφ).FiniteType :=
  sorry

namespace IsFiniteTypeOnReduction

/-- Finite type on reduction yields finite type of the induced nilradical
quotient map for any nilradical mapping inequality. -/
theorem finiteType {φ : A →+* B} (h : φ.IsFiniteTypeOnReduction)
    (h_le : topologicalNilradical A ≤ (topologicalNilradical B).comap φ) :
    (Ideal.quotientMap (topologicalNilradical B) φ h_le).FiniteType :=
  sorry

end IsFiniteTypeOnReduction

end RingHom

namespace TopologicalRing

/-- Finite type on reduction is stable under étale weak-ideal completion
squares, descends along those squares with faithfully flat target map, and is
stable under finite products of targets. -/
theorem isLocalMorphismProperty_isFiniteTypeOnReduction :
    IsLocalMorphismProperty
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
        [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
        (φ : B →+* A) ↦ φ.IsFiniteTypeOnReduction :=
  sorry

end TopologicalRing
