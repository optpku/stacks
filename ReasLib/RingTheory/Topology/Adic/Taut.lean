module

public import ReasLib.RingTheory.Topology.Adic.Basic
public import ReasLib.RingTheory.Topology.Adic.Complete
public import ReasLib.RingTheory.Topology.Adic.Hom
public import ReasLib.Topology.Algebra.Ring.Taut

/-!
# Taut homomorphisms and ideals of definition
-/

@[expose] public section

universe u v

open TopologicalRing

namespace RingHom.IsTaut

/-- The closure of the extension of an ideal of definition along a continuous taut
homomorphism is an ideal of definition. -/
theorem isIdealOfDefinition_closure_map {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut) {I : Ideal A}
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    TopologicalRing.Ideal.IsIdealOfDefinition (Ideal.map φ I).closure := sorry

/-- Pre-admissibility ascends along a continuous taut homomorphism of linearly
topologized rings. -/
theorem isPreadmissibleRing {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsPreadmissibleRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut) :
    IsPreadmissibleRing B := sorry

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [TopologicalSpace A] [IsPreadicRing A]
variable [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
variable [T2Space B] [@CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B)]

/-- The target of a continuous taut homomorphism from a pre-adic ring with a finitely
generated ideal of definition to a complete separated linearly topologized ring is adic. -/
@[stacks 0APU]
theorem isAdicRing {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut)
    (hAfg : ∃ I : Ideal A, I.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition I) :
    IsAdicRing B :=
  sorry

/-- The target of a continuous taut homomorphism from a pre-adic ring with a finitely
generated ideal of definition to a complete separated linearly topologized ring has a
finitely generated ideal of definition. -/
@[stacks 0APU]
theorem exists_fg_isIdealOfDefinition {φ : A →+* B} (hcont : Continuous φ)
    (htaut : φ.IsTaut)
    (hAfg : ∃ I : Ideal A, I.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition I) :
    ∃ J : Ideal B, J.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition J :=
  sorry

/-- A continuous taut homomorphism from a pre-adic ring with a finitely generated ideal
of definition to a complete separated linearly topologized ring admits a source ideal
of definition whose extension induces the target topology. -/
@[stacks 0APU]
theorem exists_isAdic_map {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut)
    (hAfg : ∃ I : Ideal A, I.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition I) :
    ∃ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I ∧
      IsAdic (Ideal.map φ I) :=
  sorry

/-- The extension of any finitely generated ideal of definition along a continuous taut
homomorphism from a pre-adic ring to a complete separated linearly topologized ring
induces the target topology. -/
theorem isAdic_map {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut)
    {I : Ideal A} (hIfg : I.FG) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    IsAdic (Ideal.map φ I) :=
  sorry

end

/-- A continuous taut homomorphism of pre-adic rings with complete separated target
and a finitely generated source ideal of definition is adic. -/
theorem isAdicHom {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsPreadicRing A]
    [CommRing B] [TopologicalSpace B] [IsPreadicRing B] [T2Space B]
    [@CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B)]
    {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut)
    (hAfg : ∃ I : Ideal A, I.FG ∧ TopologicalRing.Ideal.IsIdealOfDefinition I) :
    φ.IsAdicHom :=
  sorry

end RingHom.IsTaut
