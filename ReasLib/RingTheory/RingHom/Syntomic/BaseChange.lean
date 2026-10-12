/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import ReasLib.RingTheory.RingHom.Syntomic.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Base Change of Syntomic Ring Homomorphisms

This leaf owns stability of the intrinsic `RingHom.Syntomic` predicate under
the canonical tensor-product base change of commutative algebras.
-/

open scoped TensorProduct

universe u v w

namespace RingHom

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']

namespace HasLocalCompleteIntersectionFibers

/-- Local-complete-intersection fibers are preserved by arbitrary
tensor-product base change. -/
theorem baseChange (hf : (algebraMap R S).HasLocalCompleteIntersectionFibers) :
    (algebraMap R' (R' ⊗[R] S)).HasLocalCompleteIntersectionFibers := sorry

/-- Local-complete-intersection fibers descend along faithfully flat
tensor-product base change. -/
theorem iff_baseChange_of_faithfullyFlat
    (hff : (algebraMap R R').FaithfullyFlat) :
    (algebraMap R S).HasLocalCompleteIntersectionFibers ↔
      (algebraMap R' (R' ⊗[R] S)).HasLocalCompleteIntersectionFibers := sorry

end HasLocalCompleteIntersectionFibers

namespace Syntomic

/-- Lemma 10.136.3, tag 00SN: syntomic ring homomorphisms are stable under arbitrary
tensor-product base change. -/
@[stacks 00SN "syntomic base change"]
theorem baseChange (hf : (algebraMap R S).Syntomic) :
    (algebraMap R' (R' ⊗[R] S)).Syntomic := sorry

/-- Lemma 10.136.2, tag `00SM`: syntomicity is preserved and reflected by a
faithfully flat tensor-product base change. -/
@[stacks 00SM "syntomic faithfully flat base change"]
theorem iff_baseChange_of_faithfullyFlat
    (hff : (algebraMap R R').FaithfullyFlat) :
    (algebraMap R S).Syntomic ↔ (algebraMap R' (R' ⊗[R] S)).Syntomic := sorry

end Syntomic

end RingHom
