module

public import Mathlib.RingTheory.Finiteness.Defs
public import ReasLib.RingTheory.Topology.Adic.Weakly

/-!
# Finitely generated weakly adic ideals
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

/-- A complete linearly topologized ring with a finitely generated weakly adic
ideal is adic. -/
theorem isAdicRing {I : Ideal A} (hIfg : I.FG) (hI : IsWeaklyAdic I) :
    IsAdicRing A := sorry

/-- A complete linearly topologized ring with a finitely generated weakly adic
ideal has a finitely generated ideal of definition. -/
theorem exists_fg_isIdealOfDefinition {I : Ideal A} (hIfg : I.FG)
    (hI : IsWeaklyAdic I) : ∃ J : Ideal A, J.FG ∧ IsIdealOfDefinition J := sorry

end TopologicalRing.Ideal.IsWeaklyAdic

namespace TopologicalRing.IsWeaklyAdicRing

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsWeaklyAdicRing A]

/-- A weakly adic ring is adic if it has an ideal of definition whose quotient
by the closure of its square is finitely generated. -/
theorem isAdicRing {I : Ideal A} (hI : Ideal.IsIdealOfDefinition I)
    (hfg : Module.Finite A (I ⧸ Submodule.comap I.subtype (I ^ 2).closure)) :
    IsAdicRing A := sorry

/-- A weakly adic ring has a finitely generated ideal of definition if it has
an ideal of definition whose quotient by the closure of its square is finitely
generated. -/
theorem exists_fg_isIdealOfDefinition {I : Ideal A}
    (hI : Ideal.IsIdealOfDefinition I)
    (hfg : Module.Finite A (I ⧸ Submodule.comap I.subtype (I ^ 2).closure)) :
    ∃ J : Ideal A, J.FG ∧ Ideal.IsIdealOfDefinition J := sorry

end TopologicalRing.IsWeaklyAdicRing
