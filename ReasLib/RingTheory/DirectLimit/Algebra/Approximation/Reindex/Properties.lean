/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Essential
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Local
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Reindex.Core
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Properties of reindexed directed algebra approximations

Locality and essential-finite-type hypotheses are independent property layers
over an approximation.  This leaf records that they are stable under an
order-isomorphic change of stages, so downstream constructions can reindex an
approximation without rebuilding those hypotheses.
-/

@[expose] public section

universe u v w x

noncomputable section

namespace Ring.DirectLimit.Algebra.Approximation.Hom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S}

/-- Reindexing preserves the locality conditions of a directed approximation.
-/
@[stacks 00R1 "reindexed directed approximation properties"]
instance Local.reindex (A : Hom f) [A.Local] {J : Type x}
    [Preorder J] (e : J ≃o A.index) : (A.reindex e).Local := sorry

/-- Reindexing preserves the essential-finite-type conditions of a directed
approximation. -/
@[stacks 00R1 "reindexed directed approximation properties"]
instance EssFiniteType.reindex (A : Hom f) [A.EssFiniteType]
    {J : Type x} [Preorder J] (e : J ≃o A.index) :
    (A.reindex e).EssFiniteType := sorry

end Ring.DirectLimit.Algebra.Approximation.Hom
