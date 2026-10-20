/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Algebra.Ring.Taut
public import Mathlib.Order.Filter.CountablyGenerated
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Open mapping for taut homomorphisms of linearly topologized rings

A continuous taut homomorphism with dense image from a complete, countably based
linearly topologized ring to a separated one is open and surjective. Its target
is complete and is identified with the quotient by its closed kernel.
-/

@[expose] public section

universe u v

open scoped Topology

namespace RingHom.IsTaut

variable {A : Type u} {B : Type v}
variable [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
variable [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]

/-- A continuous taut homomorphism with dense image from a complete linearly
topologized ring with a countable fundamental system of open ideals to a separated
linearly topologized ring is open. -/
theorem isOpenMap [@CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)]
    [(nhds (0 : A)).IsCountablyGenerated] [T2Space B]
    {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut)
    (hdense : DenseRange φ) : IsOpenMap φ := sorry

/-- A continuous taut homomorphism with dense image from a complete linearly
topologized ring with a countable fundamental system of open ideals to a separated
linearly topologized ring is surjective. -/
theorem surjective [@CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)]
    [(nhds (0 : A)).IsCountablyGenerated] [T2Space B]
    {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut)
    (hdense : DenseRange φ) : Function.Surjective φ := sorry

/-- The kernel of a continuous taut homomorphism with dense image from a complete
linearly topologized ring with a countable fundamental system of open ideals to a
separated linearly topologized ring is closed. -/
theorem isClosed_ker [@CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)]
    [(nhds (0 : A)).IsCountablyGenerated] [T2Space B]
    {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut)
    (hdense : DenseRange φ) : IsClosed (ker φ : Set A) := sorry

/-- A continuous taut homomorphism with dense image from a complete linearly
topologized ring with a countable fundamental system of open ideals to a separated
linearly topologized ring is an open quotient map. -/
theorem isOpenQuotientMap [@CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)]
    [(nhds (0 : A)).IsCountablyGenerated] [T2Space B]
    {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut)
    (hdense : DenseRange φ) : IsOpenQuotientMap φ := sorry

/-- For a continuous taut homomorphism with dense image from a complete linearly
topologized ring with a countable fundamental system of open ideals to a separated
linearly topologized ring, the canonical map from the quotient by its kernel to
the target is a homeomorphism. -/
theorem isHomeomorph_kerLift [@CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)]
    [(nhds (0 : A)).IsCountablyGenerated] [T2Space B]
    {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut)
    (hdense : DenseRange φ) : IsHomeomorph φ.kerLift := sorry

/-- The target of a continuous taut homomorphism with dense image from a complete
linearly topologized ring with a countable fundamental system of open ideals to a
separated linearly topologized ring is complete for its additive right uniformity. -/
theorem completeSpace [@CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)]
    [(nhds (0 : A)).IsCountablyGenerated] [T2Space B]
    {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut)
    (hdense : DenseRange φ) :
    @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B) := sorry

end RingHom.IsTaut
