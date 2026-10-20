module

public import ReasLib.Topology.Algebra.Ring.Taut.OpenMapping
import StacksCheckRecall

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

variable {A : Type u} {B : Type v}
variable [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
variable [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]

/- Lemma 87.5.10: A continuous taut dense homomorphism from a complete, countably
based linearly topologized ring to a separated one is open and surjective; its
target is complete and is the quotient by its closed kernel. -/
@[stacks 0APT] #check (RingHom.IsTaut.isOpenMap :
  ∀ [@CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)]
    [(nhds (0 : A)).IsCountablyGenerated] [T2Space B] {φ : A →+* B},
    Continuous φ → φ.IsTaut → DenseRange φ → IsOpenMap φ)

#check (RingHom.IsTaut.surjective :
  ∀ [@CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)]
    [(nhds (0 : A)).IsCountablyGenerated] [T2Space B] {φ : A →+* B},
    Continuous φ → φ.IsTaut → DenseRange φ → Function.Surjective φ)

#check (RingHom.IsTaut.completeSpace :
  ∀ [@CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)]
    [(nhds (0 : A)).IsCountablyGenerated] [T2Space B] {φ : A →+* B},
    Continuous φ → φ.IsTaut → DenseRange φ →
      @CompleteSpace B (IsTopologicalAddGroup.rightUniformSpace B))

#check (RingHom.IsTaut.isHomeomorph_kerLift :
  ∀ [@CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)]
    [(nhds (0 : A)).IsCountablyGenerated] [T2Space B] {φ : A →+* B},
    Continuous φ → φ.IsTaut → DenseRange φ → IsHomeomorph φ.kerLift)

#check (RingHom.IsTaut.isClosed_ker :
  ∀ [@CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)]
    [(nhds (0 : A)).IsCountablyGenerated] [T2Space B] {φ : A →+* B},
    Continuous φ → φ.IsTaut → DenseRange φ → IsClosed (RingHom.ker φ : Set A))

#check (RingHom.IsTaut.isOpenQuotientMap :
  ∀ [@CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)]
    [(nhds (0 : A)).IsCountablyGenerated] [T2Space B] {φ : A →+* B},
    Continuous φ → φ.IsTaut → DenseRange φ → IsOpenQuotientMap φ)
