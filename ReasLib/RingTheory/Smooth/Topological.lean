module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Topological Formal Smoothness

@stack 07EB
@stack 07EF
-/

open scoped Topology

universe u v

namespace RingHom

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S]

/-- The square-zero lifting property of a formally smooth ring homomorphism, stated for ring
homomorphisms rather than bundled algebra morphisms. -/
theorem FormallySmooth.exists_lift {f : R →+* S} (hf : f.FormallySmooth) {A : Type*}
    [CommRing A] (J : Ideal A) (hJ : J ^ 2 = ⊥) (g : S →+* A ⧸ J) (g0 : R →+* A)
    (comm : (Ideal.Quotient.mk J).comp g0 = g.comp f) :
    ∃ gLift : S →+* A, (Ideal.Quotient.mk J).comp gLift = g ∧ gLift.comp f = g0 := sorry

end

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]

/-- Definition 15.37.1: a continuous ring homomorphism is topologically formally smooth when
every square-zero lifting problem with discrete quotient admits a continuous lift. -/
@[stacks 07EB "topological formal smoothness"]
class FormallySmoothTopologically (f : R →+* S) : Prop extends Continuous f where
  /-- Continuous square-zero lifting for the given ring homomorphism. -/
  lift_condition {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [DiscreteTopology A]
      (J : Ideal A) [DiscreteTopology (A ⧸ J)] (hJ : J ^ 2 = ⊥)
      (g : S →+* A ⧸ J) (hg : Continuous g)
      (g0 : R →+* A) (hg0 : Continuous g0)
      (comm : (Ideal.Quotient.mk J).comp g0 = g.comp f) :
      ∃ gLift : S →+* A, Continuous gLift ∧
        (Ideal.Quotient.mk J).comp gLift = g ∧ gLift.comp f = g0

/-- The lifting condition carried by a topologically formally smooth homomorphism. -/
theorem FormallySmoothTopologically.exists_lift {f : R →+* S} (hf : f.FormallySmoothTopologically)
    {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (J : Ideal A) [DiscreteTopology (A ⧸ J)] (hJ : J ^ 2 = ⊥)
    (g : S →+* A ⧸ J) (hg : Continuous g)
    (g0 : R →+* A) (hg0 : Continuous g0)
    (comm : (Ideal.Quotient.mk J).comp g0 = g.comp f) :
    ∃ gLift : S →+* A, Continuous gLift ∧
      (Ideal.Quotient.mk J).comp gLift = g ∧ gLift.comp f = g0 := sorry

/-- The identity of a commutative topological ring is topologically formally smooth. -/
@[stacks 07EB "identity is topologically formally smooth"]
instance FormallySmoothTopologically.id : (RingHom.id R).FormallySmoothTopologically := sorry

/-- Topological formal smoothness is stable under composition. -/
@[stacks 07EF "composition of topologically formally smooth maps"]
theorem FormallySmoothTopologically.comp {T : Type*} [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] {f : R →+* S} {g : S →+* T}
    (hf : f.FormallySmoothTopologically) (hg : g.FormallySmoothTopologically) :
    (g.comp f).FormallySmoothTopologically := sorry

/-- Composition preserves topological formal smoothness through typeclass inference. -/
@[stacks 07EF "composition instance for topological formal smoothness"]
instance FormallySmoothTopologically.instComp
    {T : Type*} [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] (f : R →+* S) (g : S →+* T)
    [f.FormallySmoothTopologically] [g.FormallySmoothTopologically] :
    (g.comp f).FormallySmoothTopologically := sorry

section

omit [TopologicalSpace S] [IsTopologicalRing S]

/-- Topological formal smoothness persists after weakening the topology on the target. -/
theorem FormallySmoothTopologically.of_le
    (f : R →+* S) {t t' : TopologicalSpace S}
    [ht : letI : TopologicalSpace S := t; IsTopologicalRing S]
    [ht' : letI : TopologicalSpace S := t'; IsTopologicalRing S]
    (h : t ≤ t')
    (hf : letI : TopologicalSpace S := t
          letI : IsTopologicalRing S := ht
          f.FormallySmoothTopologically) :
    letI : TopologicalSpace S := t'
    letI : IsTopologicalRing S := ht'
    f.FormallySmoothTopologically := sorry

end

end

end RingHom
