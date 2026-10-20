module

public import Mathlib.RingTheory.Finiteness.Defs
public import ReasLib.RingTheory.Topology.Adic.Basic
public import ReasLib.RingTheory.Topology.Adic.Complete
public import ReasLib.Topology.Algebra.Ring.Taut
public import ReasLib.Topology.Algebra.Ring.FaithfullyFlatOpenQuotients
import Mathlib.Tactic.CrossRefAttribute

/-!
# Descent of pre-admissibility and adicity

Ideals of definition and pre-admissibility descend along continuous taut
homomorphisms of linearly topologized rings with faithfully flat open quotients.
If the source is complete and separated and the target is adic with a finitely
generated ideal of definition, adicity and the existence of a finitely generated
ideal of definition descend as well.
-/

@[expose] public section

universe u v

namespace TopologicalRing.IsPreadmissibleRing

/-- If `J` is an ideal of definition of `B` and `I` is an open ideal of `A` with
`Ideal.map φ I ≤ J`, then `I` is an ideal of definition of `A`. -/
theorem isIdealOfDefinition_of {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsPreadmissibleRing B] {φ : A →+* B}
    (hcont : Continuous φ) (htaut : φ.IsTaut) (hff : φ.FaithfullyFlatOpenQuotients)
    {J : Ideal B} (hJ : TopologicalRing.Ideal.IsIdealOfDefinition J) {I : Ideal A}
    (hI : IsOpen (I : Set A)) (hmap : Ideal.map φ I ≤ J) :
    TopologicalRing.Ideal.IsIdealOfDefinition I :=
  sorry

/-- Pre-admissibility descends along a continuous taut homomorphism of linearly
topologized rings whose canonical quotients by open ideals and the closures of
their extensions are faithfully flat. -/
@[stacks 0GXN]
theorem of_isTaut {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsPreadmissibleRing B] {φ : A →+* B}
    (hcont : Continuous φ) (htaut : φ.IsTaut) (hff : φ.FaithfullyFlatOpenQuotients) :
    IsPreadmissibleRing A :=
  sorry

end TopologicalRing.IsPreadmissibleRing

namespace TopologicalRing.IsAdicRing

/-- A complete separated linearly topologized ring is adic if it admits a continuous
taut homomorphism with faithfully flat open quotients to an adic ring with a
finitely generated ideal of definition. -/
@[stacks 0GXQ]
theorem of_faithfullyFlatOpenQuotients {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [T2Space A] [@CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] {φ : A →+* B}
    (hcont : Continuous φ) (htaut : φ.IsTaut) (hff : φ.FaithfullyFlatOpenQuotients)
    (hBfg : ∃ J : Ideal B, J.FG ∧ Ideal.IsIdealOfDefinition J) :
    IsAdicRing A :=
  sorry

/-- A complete separated linearly topologized ring has a finitely generated ideal
of definition if it admits a continuous taut homomorphism with faithfully flat
open quotients to an adic ring with a finitely generated ideal of definition. -/
@[stacks 0GXQ]
theorem exists_fg_isIdealOfDefinition {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [T2Space A] [@CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] {φ : A →+* B}
    (hcont : Continuous φ) (htaut : φ.IsTaut) (hff : φ.FaithfullyFlatOpenQuotients)
    (hBfg : ∃ J : Ideal B, J.FG ∧ Ideal.IsIdealOfDefinition J) :
    ∃ I : Ideal A, I.FG ∧ Ideal.IsIdealOfDefinition I :=
  sorry

end TopologicalRing.IsAdicRing
