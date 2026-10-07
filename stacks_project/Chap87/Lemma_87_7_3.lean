module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Topology.Adic.Complete
public import stacks_project.Chap87.Definition_87_7_1_WeaklyAdic

/-!
# Lemma 87.7.3

A complete linearly topologized ring with a finitely generated weakly adic
ideal is adic and has a finitely generated ideal of definition.
-/

@[expose] public section

universe u

open TopologicalRing

namespace TopologicalRing.Ideal.IsWeaklyAdic

variable {A : Type u} [CommRing A] [TopologicalSpace A]
variable [IsTopologicalRing A] [IsLinearTopology A A] [T2Space A]
variable [@CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)]

/-- If `I` is a finitely generated weakly adic ideal of a complete linearly
topologized ring, then the ambient topology is the `I`-adic topology. -/
theorem isAdic {I : Ideal A} (hIfg : I.FG) (hI : IsWeaklyAdic I) : IsAdic I := sorry

/-- If `I` is a finitely generated weakly adic ideal of a complete linearly
topologized ring, then `I` is an ideal of definition. -/
theorem isIdealOfDefinition {I : Ideal A} (hIfg : I.FG) (hI : IsWeaklyAdic I) :
    IsIdealOfDefinition I := sorry

/-- Lemma 87.7.3 (1): Let `A` be a complete linearly topologized ring. Let `I`
be a finitely generated ideal such that the closure of `I ^ n` is open for all
`n ≥ 0` and these closures form a fundamental system of open ideals. Then `A`
is adic. -/
@[stacks 0GXG]
theorem isAdicRing {I : Ideal A} (hIfg : I.FG) (hI : IsWeaklyAdic I) :
    IsAdicRing A := sorry

/-- Lemma 87.7.3 (2): Let `A` be a complete linearly topologized ring. Let `I`
be a finitely generated ideal such that the closure of `I ^ n` is open for all
`n ≥ 0` and these closures form a fundamental system of open ideals. Then `A`
has a finitely generated ideal of definition. -/
@[stacks 0GXG]
theorem exists_fg_isIdealOfDefinition {I : Ideal A} (hIfg : I.FG)
    (hI : IsWeaklyAdic I) : ∃ J : Ideal A, J.FG ∧ IsIdealOfDefinition J := sorry

end TopologicalRing.Ideal.IsWeaklyAdic
