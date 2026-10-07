module

public import ReasLib.FieldTheory.Transcendence.FiniteType
public import ReasLib.RingTheory.KrullDimension.FiniteType.Local
public import ReasLib.RingTheory.KrullDimension.Prime
public import ReasLib.Topology.KrullDimension.Local
public import ReasLib.AlgebraicGeometry.PrimeSpectrum.Notation
import StacksCheckRecall

/-!
# Isolated points of a finite type spectrum

@stack 00PJ

The prime-spectrum, localization, transcendence, and idempotent-product
primitives are owned by the imported library leaves.  This file retains the
six source clauses and the finite-type complementary-factor conclusion.
-/

@[expose] public section

universe u v

open PrimeSpectrum
open TopologicalSpace
open scoped PrimeSpectrum

section

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

/-- Closed points of a finite type algebra have finite residue fields over the base field. -/
@[stacks 00PJ "closed point and finite residue field"]
theorem isClosed_singleton_iff_moduleFinite_residueField (q : PrimeSpectrum S) :
    IsClosed ({q} : Set (PrimeSpectrum S)) ↔
      Module.Finite k q.asIdeal.ResidueField := sorry

/- Lemma 10.122.1 (00PJ): for a prime `q` of a finite type `k`-algebra `S`,
the six isolated-point, localization, basic-open, dimension, closed-point, and
residue-field conditions are equivalent. -/
@[stacks 00PJ "source six-clause form"]
#check fun q : PrimeSpectrum S => show
  List.TFAE
    [ IsOpen ({q} : Set (PrimeSpectrum S))
    , Module.Finite k (Localization.AtPrime q.asIdeal)
    , ∃ g : S, g ∉ q.asIdeal ∧ (D(g) : Set (PrimeSpectrum S)) = {q}
    , topologicalKrullDimAt q = 0
    , IsClosed ({q} : Set (PrimeSpectrum S)) ∧
        ringKrullDim (Localization.AtPrime q.asIdeal) = 0
    , Module.Finite k q.asIdeal.ResidueField ∧
        ringKrullDim (Localization.AtPrime q.asIdeal) = 0
    ] from by sorry

/-- Lemma 10.122.1 (00PJ), complementary factor: an isolated point gives a
finite type product decomposition whose first projection is the AtPrime
localization map. -/
@[stacks 00PJ "complementary factor"]
theorem exists_finiteType_complementary_factor_of_isolatedPoint
    (q : PrimeSpectrum S) (hq : IsOpen ({q} : Set (PrimeSpectrum S))) :
    ∃ (S' : Type v) (_ : CommRing S') (_ : Algebra k S') (_ : Algebra.FiniteType k S')
      (e : S ≃ₐ[k] Localization.AtPrime q.asIdeal × S'),
      (RingHom.fst (Localization.AtPrime q.asIdeal) S').comp e.toRingHom =
        algebraMap S (Localization.AtPrime q.asIdeal) := sorry

/-! Canonical owner checks retained for downstream navigation. -/

@[stacks 00PJ "isolated-point topology criterion"]
#check @PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing

@[stacks 00PJ "basic-open localization criterion"]
#check @PrimeSpectrum.isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton

end
