/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.Separable.Generated.Properties
public import ReasLib.RingTheory.KrullDimension.FiniteType.Local
public import ReasLib.RingTheory.Smooth.AtPrime
public import ReasLib.RingTheory.Smooth.Local.Regularity

/-!
# Regularity criteria for smooth algebras over fields

This leaf separates the reusable local regularity facts from the textbook
presentation by a `List.TFAE`.  The numerical criteria use the intrinsic
point dimension `topologicalKrullDimAt` rather than a chosen decomposition
into local Krull dimension and residue transcendence degree.
@stack 00TT
@stack 00TS
@stack 00TV
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Algebra.IsSmoothAt

/-- Tag `00TT`: smoothness at a prime of an essentially finite-type field algebra implies that
its prime localization is regular local. -/
@[stacks 00TT "regularity at a smooth prime over a field"]
theorem isRegularLocalRing
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    [Algebra.EssFiniteType k S] (q : Ideal S) [q.IsPrime]
    (hSmooth : Algebra.IsSmoothAt k q) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  -- Local instance justification (proof-local temporary data): the explicit smooth-at-prime
  -- hypothesis is the class fact required by the localized formal-smooth regularity theorem.
  letI : Algebra.FormallySmooth k (Localization.AtPrime q) := hSmooth
  exact Algebra.FormallySmooth.isRegularLocalRing
    (k := k) (A := Localization.AtPrime q)

/-- Lemma 10.140.5, tag `00TV`: at a prime of a finite type field algebra with separable residue
field, smoothness is equivalent to regularity of the prime localization. -/
@[stacks 00TV "smoothness and regularity with separable residue field"]
theorem iff_isRegularLocalRing_of_separableResidueField
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (q : Ideal S) [q.IsPrime]
    [Algebra.IsSeparableOver k q.ResidueField] :
    Algebra.IsSmoothAt k q ↔ IsRegularLocalRing (Localization.AtPrime q) := sorry

end Algebra.IsSmoothAt

namespace Algebra.IsSmoothAt

/-- Tag `00TT`: smoothness at a point is characterized by the upper Kähler-fiber dimension
bound against its intrinsic local topological dimension. -/
@[stacks 00TT "smoothness by Kähler-fiber dimension bound"]
theorem iff_finrank_kaehlerFiber_le_topologicalKrullDimAt
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (q : PrimeSpectrum S) :
    Algebra.IsSmoothAt k q.asIdeal ↔
      Module.finrank q.asIdeal.ResidueField (q.asIdeal.ResidueField ⊗[S] Ω[S⁄k]) ≤
        topologicalKrullDimAt q := sorry

/-- Tag `00TT`: smoothness at a point is characterized by equality of its Kähler-fiber dimension
and intrinsic local topological dimension. -/
@[stacks 00TT "smoothness by Kähler-fiber dimension equality"]
theorem iff_finrank_kaehlerFiber_eq_topologicalKrullDimAt
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (q : PrimeSpectrum S) :
    Algebra.IsSmoothAt k q.asIdeal ↔
      Module.finrank q.asIdeal.ResidueField (q.asIdeal.ResidueField ⊗[S] Ω[S⁄k]) =
        topologicalKrullDimAt q := sorry

end Algebra.IsSmoothAt

namespace Algebra.SmoothAtPrime

variable {k : Type u} {S : Type v}
variable [Field k] [CommRing S] [Algebra k S]
variable [Algebra.FiniteType k S] [IsAlgClosed k]

/-- At a closed point of a finite-type algebra over an algebraically closed field,
smoothness at the corresponding prime is equivalent to regularity of its local ring. -/
theorem iff_isRegularLocalRing_at_maximal (m : MaximalSpectrum S) :
    Algebra.SmoothAtPrime k S m.toPrimeSpectrum ↔
      IsRegularLocalRing (Localization.AtPrime m.asIdeal) := by
  -- Local instance justification (proof-local temporary data): over the field `k`, finite type
  -- yields finite presentation, required by the principal-open/local-predicate bridge below.
  letI : Algebra.FinitePresentation k S :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  -- Local instance justification (proof-local temporary data): algebraic closedness makes `k`
  -- perfect, supplying the residue separability class required by the regularity criterion.
  letI : Algebra.IsSeparableOver k m.asIdeal.ResidueField :=
    Algebra.IsSeparableOver.of_perfectField
  exact (Algebra.SmoothAtPrime.iff_isSmoothAt k S m.toPrimeSpectrum).trans
    (Algebra.IsSmoothAt.iff_isRegularLocalRing_of_separableResidueField m.asIdeal)

omit [IsAlgClosed k] in
/-- At a closed point, the Kähler-fiber finrank bound is equivalent to smoothness,
using the residue field attached to the maximal ideal. -/
theorem iff_fiberFinrank_le_localDimension_at_maximal (m : MaximalSpectrum S) :
    Algebra.SmoothAtPrime k S m.toPrimeSpectrum ↔
      Module.finrank m.asIdeal.ResidueField
          (m.asIdeal.ResidueField ⊗[S] Ω[S⁄k]) ≤
        ringKrullDim (Localization.AtPrime m.asIdeal) := by
  -- Local instance justification (proof-local temporary data): over the field `k`, finite type
  -- yields finite presentation, required by the principal-open/local-predicate bridge below.
  letI : Algebra.FinitePresentation k S :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hdim :=
    MaximalSpectrum.topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime
      (F := k) (A := S) m
  rw [Algebra.SmoothAtPrime.iff_isSmoothAt,
    Algebra.IsSmoothAt.iff_finrank_kaehlerFiber_le_topologicalKrullDimAt,
    hdim]
  simp only [MaximalSpectrum.toPrimeSpectrum]
  rfl

omit [IsAlgClosed k] in
/-- At a closed point, equality of Kähler-fiber finrank and local dimension is
equivalent to smoothness. -/
theorem iff_fiberFinrank_eq_localDimension_at_maximal (m : MaximalSpectrum S) :
    Algebra.SmoothAtPrime k S m.toPrimeSpectrum ↔
      Module.finrank m.asIdeal.ResidueField
          (m.asIdeal.ResidueField ⊗[S] Ω[S⁄k]) =
        ringKrullDim (Localization.AtPrime m.asIdeal) := by
  -- Local instance justification (proof-local temporary data): over the field `k`, finite type
  -- yields finite presentation, required by the principal-open/local-predicate bridge below.
  letI : Algebra.FinitePresentation k S :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hdim :=
    MaximalSpectrum.topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime
      (F := k) (A := S) m
  rw [Algebra.SmoothAtPrime.iff_isSmoothAt,
    Algebra.IsSmoothAt.iff_finrank_kaehlerFiber_eq_topologicalKrullDimAt,
    hdim]
  simp only [MaximalSpectrum.toPrimeSpectrum]
  rfl

omit [IsAlgClosed k] in
/-- The closed-point finrank bound and equality formulations are equivalent. -/
theorem fiberFinrank_le_iff_eq_at_maximal (m : MaximalSpectrum S) :
    Module.finrank m.asIdeal.ResidueField
          (m.asIdeal.ResidueField ⊗[S] Ω[S⁄k]) ≤
        ringKrullDim (Localization.AtPrime m.asIdeal) ↔
      Module.finrank m.asIdeal.ResidueField
          (m.asIdeal.ResidueField ⊗[S] Ω[S⁄k]) =
        ringKrullDim (Localization.AtPrime m.asIdeal) :=
  (iff_fiberFinrank_le_localDimension_at_maximal m).symm.trans
    (iff_fiberFinrank_eq_localDimension_at_maximal m)

end Algebra.SmoothAtPrime
