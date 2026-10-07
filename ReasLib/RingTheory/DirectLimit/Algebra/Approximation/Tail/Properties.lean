module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Essential
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Local
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Tail.Core
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Approximation properties on cofinal tails

This leaf transports optional property layers of a directed approximation to
any cofinal tail.  The resulting facts are canonical instances, so consumers
can apply locality and essential-finiteness APIs to a tail without rebuilding
the corresponding stagewise bundles.
-/

@[expose] public section

universe u v

namespace Ring.DirectLimit.Algebra.Approximation.Hom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S}

/-- Restricting an approximation to a cofinal tail preserves its locality
conditions. -/
@[stacks 00R1 "directed approximation tail properties"]
instance Local.tail (A : Hom f) [A.Local] (i₀ : A.index) :
    (A.tail i₀).Local := sorry

/-- Restricting an approximation to a cofinal tail preserves its
essential-finite-type conditions. -/
@[stacks 00R1 "directed approximation tail properties"]
instance EssFiniteType.tail (A : Hom f) [A.EssFiniteType] (i₀ : A.index) :
    (A.tail i₀).EssFiniteType := sorry

end Ring.DirectLimit.Algebra.Approximation.Hom
