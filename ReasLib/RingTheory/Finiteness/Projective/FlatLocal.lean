/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Finiteness.Projective.BaseChange
public import ReasLib.RingTheory.Finiteness.Projective.LocalRing

/-!
# Finite Projective Modules and Flat Local Homomorphisms

This leaf specializes faithfully-flat descent to a flat local homomorphism of
local rings.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Module.FiniteProjective

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M]

/-- Lemma 10.78.6, tag `00O1`: finite projectivity is detected after a flat local
homomorphism of local rings. -/
@[stacks 00O1 "finite projective modules and flat local homomorphisms"]
theorem iff_tensorProduct_of_flat_localHom [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S] :
    Module.FiniteProjective R M ↔ Module.FiniteProjective S (S ⊗[R] M) := by
  letI : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  constructor
  · exact Module.FiniteProjective.baseChange
  · intro hM
    letI := hM.finite
    letI := hM.projective
    have hfinite : Module.Finite R M :=
      Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S
    have hflat : Module.Flat R M := Module.Flat.of_flat_tensorProduct R M S
    exact Module.FiniteProjective.of_finite_flat_of_localRing hfinite hflat

end Module.FiniteProjective
