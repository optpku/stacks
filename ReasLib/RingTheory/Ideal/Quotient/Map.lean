/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Quotient algebra actions induced by explicit ring maps

Mathlib's quotient algebra instance is convenient when the ambient algebra map
is canonical. This leaf records the corresponding explicit action when a
particular ring homomorphism is the semantic owner of the mapped ideal.

@stack 051T
-/

@[expose] public section

universe u v

namespace Ideal.Quotient

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- The quotient algebra action induced by an explicit ring homomorphism `f`.  This is not a
global instance, since two maps with the same source and target can induce different actions. -/
@[stacks 051T "explicit mapped-ideal quotient action"]
noncomputable abbrev mapAlgebra (f : A →+* B) (I : Ideal A) :
    Algebra (A ⧸ I) (B ⧸ I.map f) :=
  (Ideal.quotientMap (I.map f) f Ideal.le_comap_map).toAlgebra

/-- Under `mapAlgebra`, the quotient algebra map sends a representative to the representative of
its image under the chosen ring homomorphism. -/
@[stacks 051T "explicit mapped-ideal quotient representative"]
theorem mapAlgebra_apply_mk (f : A →+* B) (I : Ideal A) (x : A) :
    letI : Algebra (A ⧸ I) (B ⧸ I.map f) := mapAlgebra f I
    algebraMap (A ⧸ I) (B ⧸ I.map f) (Ideal.Quotient.mk I x) =
      Ideal.Quotient.mk (I.map f) (f x) := sorry

end Ideal.Quotient
