module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Order.Antichain
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.Topology.Connected.TotallyDisconnected
public import ReasLib.RingTheory.Algebraic.ResidueField

/-!
# Profinite spectra along algebra maps

This module records preservation of total disconnectedness of prime spectra
under fiberwise incomparability, residue-field algebraicity, étale-related
hypotheses, and filtered colimits.
-/

@[expose] public section

open CategoryTheory Limits CommRingCat Topology

universe u v

namespace Algebra

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Fibers of `Spec(S) → Spec(R)` are antichains for inclusion of primes. -/
def IsAntichainOnFibers (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] : Prop :=
  ∀ p : PrimeSpectrum R,
    IsAntichain (· ≤ ·) (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p})

namespace IsAntichainOnFibers

/-- Fiberwise incomparability is equivalent to: primes over the same prime of `R`
that specialize are equal. -/
theorem iff :
    IsAntichainOnFibers R S ↔
      ∀ ⦃q q' : PrimeSpectrum S⦄,
        PrimeSpectrum.comap (algebraMap R S) q = PrimeSpectrum.comap (algebraMap R S) q' →
          q ⤳ q' → q = q' := sorry

/-- In an antichain fiber, specialization implies equality. -/
theorem eq_of_specializes (h : IsAntichainOnFibers R S) {q q' : PrimeSpectrum S}
    (hcomap :
      PrimeSpectrum.comap (algebraMap R S) q = PrimeSpectrum.comap (algebraMap R S) q')
    (hspec : q ⤳ q') : q = q' := sorry

/-- Quasi-finite algebras have antichain fibers. -/
theorem of_quasiFinite [QuasiFinite R S] : IsAntichainOnFibers R S := sorry

end IsAntichainOnFibers

end Algebra

namespace PrimeSpectrum

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- If `Spec(R)` is totally disconnected and fibers of `Spec(S) → Spec(R)` are
antichains, then `Spec(S)` is totally disconnected. -/
theorem isTotallyDisconnected_univ_of_isAntichainOnFibers
    [TotallyDisconnectedSpace (PrimeSpectrum R)]
    (h : Algebra.IsAntichainOnFibers R S) :
    IsTotallyDisconnected (Set.univ : Set (PrimeSpectrum S)) := sorry

/-- If `Spec(R)` is totally disconnected and residue-field extensions are algebraic,
then `Spec(S)` is totally disconnected. -/
theorem isTotallyDisconnected_univ_of_isAlgebraicOnResidueFields
    [TotallyDisconnectedSpace (PrimeSpectrum R)]
    (h : Algebra.IsAlgebraicOnResidueFields R S) :
    IsTotallyDisconnected (Set.univ : Set (PrimeSpectrum S)) := sorry

/-- A local isomorphism preserves total disconnectedness of prime spectra. -/
theorem isTotallyDisconnected_univ_of_isLocalIso
    [TotallyDisconnectedSpace (PrimeSpectrum R)] [Algebra.IsLocalIso R S] :
    IsTotallyDisconnected (Set.univ : Set (PrimeSpectrum S)) := sorry

/-- A weakly étale algebra over a ring with totally disconnected spectrum again
has totally disconnected spectrum. -/
theorem isTotallyDisconnected_univ_of_weaklyEtale
    [TotallyDisconnectedSpace (PrimeSpectrum R)] [Algebra.WeaklyEtale R S] :
    IsTotallyDisconnected (Set.univ : Set (PrimeSpectrum S)) := sorry

/-- A finite-type quasi-finite algebra over a ring with totally disconnected
spectrum again has totally disconnected spectrum. -/
theorem isTotallyDisconnected_univ_of_quasiFinite
    [TotallyDisconnectedSpace (PrimeSpectrum R)] [Algebra.FiniteType R S]
    [Algebra.QuasiFinite R S] :
    IsTotallyDisconnected (Set.univ : Set (PrimeSpectrum S)) := sorry

/-- An unramified algebra over a ring with totally disconnected spectrum again
has totally disconnected spectrum. -/
theorem isTotallyDisconnected_univ_of_unramified
    [TotallyDisconnectedSpace (PrimeSpectrum R)] [Algebra.Unramified R S] :
    IsTotallyDisconnected (Set.univ : Set (PrimeSpectrum S)) := sorry

/-- An étale algebra over a ring with totally disconnected spectrum again has
totally disconnected spectrum. -/
theorem isTotallyDisconnected_univ_of_etale
    [TotallyDisconnectedSpace (PrimeSpectrum R)] [Algebra.Etale R S] :
    IsTotallyDisconnected (Set.univ : Set (PrimeSpectrum S)) := sorry

end PrimeSpectrum

namespace PrimeSpectrum

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Identifying local rings preserves total disconnectedness of prime spectra. -/
theorem isTotallyDisconnected_univ_of_isIsoOnLocalRings
    [TotallyDisconnectedSpace (PrimeSpectrum R)]
    (h : (algebraMap R S).IsIsoOnLocalRings) :
    IsTotallyDisconnected (Set.univ : Set (PrimeSpectrum S)) := sorry

end PrimeSpectrum

namespace PrimeSpectrum

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {J : Type v} [Category.{v} J] [IsFiltered J]

/-- A filtered colimit of algebras with totally disconnected spectra again has
totally disconnected spectrum. -/
theorem isTotallyDisconnected_univ_of_isColimit
    (F : J ⥤ Under (CommRingCat.of R)) (c : Cocone F) (hc : IsColimit c)
    (e : c.pt ≅ Under.mk (CommRingCat.ofHom (algebraMap R A)))
    (hF : ∀ j, IsTotallyDisconnected
      (Set.univ : Set (PrimeSpectrum (F.obj j).right))) :
    IsTotallyDisconnected (Set.univ : Set (PrimeSpectrum A)) := sorry

end PrimeSpectrum
