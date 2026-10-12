/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Order.Filter.CountablyGenerated
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
public import stacks_project.Chap87.Definition_87_5_1_Taut

/-!
# Lemma 87.5.10

A continuous taut homomorphism of linearly topologized rings with dense image,
from a complete source with a countable fundamental system of open ideals to a
separated target, is surjective and open; the target is complete and identifies
with the quotient by the kernel.
-/

@[expose] public section

universe u v

open scoped Topology

namespace RingHom.IsTaut

variable {A : Type u} {B : Type v}
variable [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
variable [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
variable [@CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)]
variable [(nhds (0 : A)).IsCountablyGenerated] [T2Space B]

/-- Lemma 87.5.10 (1): Let `φ : A →+* B` be a continuous homomorphism of linearly
topologized rings. If `φ` is taut and has dense image, `A` is complete and has a
countable fundamental system of open ideals, and `B` is separated, then `φ` is
open. -/
@[stacks 0APT]
theorem isOpenMap {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut)
    (hdense : DenseRange φ) : IsOpenMap φ :=
  sorry

/-- Lemma 87.5.10 (2): Let `φ : A →+* B` be a continuous homomorphism of linearly
topologized rings. If `φ` is taut and has dense image, `A` is complete and has a
countable fundamental system of open ideals, and `B` is separated, then `φ` is
surjective. -/
@[stacks 0APT]
theorem surjective {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut)
    (hdense : DenseRange φ) : Function.Surjective φ :=
  sorry

/-- Lemma 87.5.10 (3): Let `φ : A →+* B` be a continuous homomorphism of linearly
topologized rings. If `φ` is taut and has dense image, `A` is complete and has a
countable fundamental system of open ideals, and `B` is separated, then `B` is
complete. -/
@[stacks 0APT]
theorem completeSpace {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut)
    (hdense : DenseRange φ) :
    @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B) :=
  sorry

/-- Lemma 87.5.10 (4): Let `φ : A →+* B` be a continuous homomorphism of linearly
topologized rings. If `φ` is taut and has dense image, `A` is complete and has a
countable fundamental system of open ideals, and `B` is separated, then `B`
identifies with `A ⧸ ker φ` as topological rings. -/
@[stacks 0APT]
theorem isHomeomorph_quotientKerEquiv {φ : A →+* B} (hcont : Continuous φ)
    (htaut : φ.IsTaut) (hdense : DenseRange φ) :
    IsHomeomorph (φ.quotientKerEquivOfSurjective (surjective hcont htaut hdense)) :=
  sorry

/-- The kernel of a continuous taut homomorphism with dense image, from a complete
linearly topologized ring with a countable fundamental system of open ideals to a
separated target, is closed. -/
theorem isClosed_ker {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut)
    (hdense : DenseRange φ) : IsClosed (ker φ : Set A) :=
  sorry

/-- A continuous taut homomorphism with dense image, from a complete linearly
topologized ring with a countable fundamental system of open ideals to a
separated target, is an open quotient map. -/
theorem isOpenQuotientMap {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut)
    (hdense : DenseRange φ) : IsOpenQuotientMap φ :=
  sorry

end RingHom.IsTaut
