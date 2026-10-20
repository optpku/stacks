/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Etale.StandardEtale

@[expose] public section

universe u v

namespace RingHom

/-- A ring homomorphism is standard étale if its target is a standard étale
algebra for the algebra structure induced by that homomorphism. -/
def IsStandardEtale {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (hom : R →+* S) : Prop :=
  @Algebra.IsStandardEtale R S _ _ hom.toAlgebra

/-- An algebra map is standard étale exactly when its target is a standard
étale algebra over its source. -/
theorem isStandardEtale_algebraMap {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S] :
    RingHom.IsStandardEtale (algebraMap R S) ↔ Algebra.IsStandardEtale R S := sorry

end RingHom
