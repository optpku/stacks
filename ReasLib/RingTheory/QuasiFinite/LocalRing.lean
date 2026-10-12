/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.EssFiniteType
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Localization.Basic
public import ReasLib.RingTheory.QuasiFinite.FiniteType

open IsLocalRing

universe u v

@[expose] public section

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [Algebra A B] [IsLocalRing A] [IsLocalRing B]
variable [IsLocalHom (algebraMap A B)] [IsNoetherianRing A]
variable [Algebra.EssFiniteType A B]
variable [Module.Finite (ResidueField A) (ResidueField B)]

namespace Algebra.EssFiniteType

/-- For a local essentially finite-type map from a Noetherian local ring with
finite residue-field extension, an open subset containing a point away from
the closed fibre contains a prime whose quotient is a localization of a
finite-type quasi-finite algebra. -/
@[stacks 05GT]
theorem exists_prime_mem_open_localization_quasiFinite
    (V : TopologicalSpace.Opens (PrimeSpectrum B))
    (hV : ∃ p : PrimeSpectrum B,
      p ∈ V ∧ IsLocalRing.maximalIdeal A ≠
        p.asIdeal.comap (algebraMap A B)) :
    ∃ q : PrimeSpectrum B,
      q ∈ V ∧ IsLocalRing.maximalIdeal A ≠
        q.asIdeal.comap (algebraMap A B) ∧
      ∃ (C : Subalgebra A (B ⧸ q.asIdeal)) (M : Submonoid C),
        Algebra.FiniteType.QuasiFinite A C ∧
          IsLocalization M (B ⧸ q.asIdeal) := sorry

end Algebra.EssFiniteType

end

end
