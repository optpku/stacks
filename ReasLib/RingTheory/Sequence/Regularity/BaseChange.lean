/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Sequence.Regularity

/-!
# Regular sequences under faithfully flat base change

The faithfully-flat tensor statement is the canonical owner.  Flat local
base change is exposed as a source-facing specialization, and self-module
specializations are exposed separately so callers do not have to rebuild the
tensor-unit equivalence.

@stack 00LM
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace RingTheory.Sequence.IsRegular

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M]

/- The tensor-product form is the reusable faithfully-flat owner. -/
/-- Faithfully flat tensor base change detects regular sequences without
requiring local or Noetherian hypotheses. -/
theorem iff_tensorProduct_of_faithfullyFlat [Module.FaithfullyFlat R S]
    {rs : List R} :
    IsRegular M rs ↔
      IsRegular (S ⊗[R] M) (rs.map (algebraMap R S)) := sorry

/-- Faithfully flat base change detects regular sequences on the self-module. -/
theorem iff_map_of_faithfullyFlat [Module.FaithfullyFlat R S] {rs : List R} :
    IsRegular R rs ↔ IsRegular S (rs.map (algebraMap R S)) := sorry

/- The local flat theorem is the exact source-facing bridge. -/
/-- Lemma 10.68.5 (Stacks tag `00LM`): over a flat local homomorphism of
local rings, regularity of a finite sequence is equivalent to regularity of
its image on the tensor base change. -/
@[stacks 00LM "regular sequences under flat local base change"]
theorem iff_tensorProduct_of_flat_localHom [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S] {rs : List R} :
    IsRegular M rs ↔
      IsRegular (S ⊗[R] M) (rs.map (algebraMap R S)) := sorry

/- The self-module form is a thin canonical specialization of the tensor owner. -/
/-- A flat local algebra map preserves regular sequences on the self-module,
with the entries transported by `algebraMap`. -/
theorem iff_map_of_flat_localHom [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S] {rs : List R} :
    IsRegular R rs ↔ IsRegular S (rs.map (algebraMap R S)) := sorry

end RingTheory.Sequence.IsRegular
