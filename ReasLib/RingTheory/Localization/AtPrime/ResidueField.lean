module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import ReasLib.RingTheory.LocalRing.ResidueField.MaximalIdeal
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Residue fields of prime localizations

The residue field of the prime localization `Rₚ` is canonically the residue
field of `p`. This is the reusable ring-level comparison; chapter files can
add algebra or scalar-tower corollaries without rebuilding the equivalence.
@stack 0BRM
@stack 04GW
-/

universe u v

namespace Localization.AtPrime

/-- The maximal-ideal residue field of `Rₚ` is canonically the residue field
of `p`. -/
@[stacks 0BRM "residue field of a prime localization"]
noncomputable def residueFieldEquiv
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] :
    (IsLocalRing.maximalIdeal (Localization.AtPrime p)).ResidueField ≃+*
      p.ResidueField := by
  change (IsLocalRing.maximalIdeal (Localization.AtPrime p)).ResidueField ≃+*
      IsLocalRing.ResidueField (Localization.AtPrime p)
  exact (IsLocalRing.ResidueField.maximalIdealAlgEquiv
    (Localization.AtPrime p)).symm.toRingEquiv

/-- The canonical map from the residue field of `Rₚ` to any algebra over
`κ(p)`.  It is constructed solely from the canonical residue-field
identification, so it introduces no choice of a kernel proof or scalar tower. -/
@[stacks 04GW "canonical map from a prime-local residue field"]
noncomputable def residueMapOfAlgebra
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    {K : Type v} [CommRing K] [Algebra p.ResidueField K] :
    IsLocalRing.ResidueField (Localization.AtPrime p) →+* K :=
  (algebraMap p.ResidueField K).comp
    ((residueFieldEquiv p).toRingHom.comp
      (IsLocalRing.ResidueField.maximalIdealAlgEquiv
        (Localization.AtPrime p)).toRingHom)

/-- Evaluation of the canonical prime-local residue map through the two
canonical residue-field identifications. -/
@[stacks 04GW "evaluation of the canonical prime-local residue map"]
theorem residueMapOfAlgebra_apply
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    {K : Type v} [CommRing K] [Algebra p.ResidueField K]
    (x : IsLocalRing.ResidueField (Localization.AtPrime p)) :
    residueMapOfAlgebra p x =
      algebraMap p.ResidueField K
        (residueFieldEquiv p
          (IsLocalRing.ResidueField.maximalIdealAlgEquiv
            (Localization.AtPrime p) x)) := sorry

/-- The residue-field equivalence of prime localizations intertwines the
canonical map induced by `Localization.localRingHom` with the map of residue
fields induced by the original ring homomorphism. -/
@[stacks 04GW "prime-local residue-field map naturality"]
theorem residueFieldMap_naturality
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime]
    (h_comap : p = Ideal.comap (algebraMap A B) q) :
    let f := Localization.localRingHom p q (algebraMap A B) h_comap
    (residueFieldEquiv q).toRingHom.comp
        (Ideal.ResidueField.map
          (IsLocalRing.maximalIdeal (Localization.AtPrime p))
          (IsLocalRing.maximalIdeal (Localization.AtPrime q))
          f (IsLocalRing.maximalIdeal_comap f).symm) =
      (Ideal.ResidueField.map p q (algebraMap A B) h_comap).comp
        (residueFieldEquiv p).toRingHom := sorry

end Localization.AtPrime
