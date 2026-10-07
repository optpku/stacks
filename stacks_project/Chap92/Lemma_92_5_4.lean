module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import stacks_project.Chap110.Lemma_110_43_1_Cotangent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite André-Quillen homology of finite-type algebras

Lemma 92.5.4 records that if `A` is Noetherian and `A → B` is of finite type, then every
cohomology module of the André-Quillen complex `L_{B/A}` is a finite `B`-module.
-/

@[expose] public section

universe u

namespace Algebra.CotangentComplex

section

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable [IsNoetherianRing A] [Algebra.FiniteType A B]

/-- Lemma 92.5.4. Let `A` be a Noetherian ring. Let `A → B` be a finite type ring map.
Then `H^n(L_{B/A})` is a finite `B`-module for all `n : ℤ`. -/
@[stacks 08PZ]
instance homology_finite (n : ℤ) :
    Module.Finite B ((Algebra.cotangentComplex A B).homology n) :=
  sorry

end

/-- The André-Quillen homology of a finite-type ring homomorphism from a Noetherian
source is a finite module over the codomain. -/
theorem homology_finite_ringHom {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) [IsNoetherianRing A] (hf : f.FiniteType) (n : ℤ) :
    Module.Finite B ((RingHom.cotangentComplex f).homology n) :=
  sorry

end Algebra.CotangentComplex
