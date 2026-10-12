/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap72.Definition_72_6_2_Prime
public import stacks_project.Chap72.Lemma_72_6_3_Comparison

/-!
# Henselian local rings at generic points of prime divisors

On a locally Noetherian integral algebraic space, the henselian local ring at the
generic point of a prime divisor is a reduced 1-dimensional Noetherian local ring,
and the function field embeds canonically into its total ring of fractions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable [h_locallyNoetherian : IsLocallyNoetherian X] [h_integral : IsIntegral X]

include h_locallyNoetherian h_integral

/-- Lemma 72.6.3 (1): let `Z ⊂ X` be a prime divisor with generic point
`ξ = Z.genericPoint`. Then `henselianLocalRing X ξ` is reduced. -/
@[stacks 0ENK, instance]
instance instIsReduced_henselianLocalRing_genericPoint (Z : PrimeDivisor X) :
    _root_.IsReduced (henselianLocalRing X Z.genericPoint) :=
  let _ := h_locallyNoetherian
  sorry

/-- Lemma 72.6.3 (2): let `Z ⊂ X` be a prime divisor with generic point
`ξ = Z.genericPoint`. Then `henselianLocalRing X ξ` is Noetherian. Locality is
the existing `HenselianLocalRing` instance. -/
@[stacks 0ENK, instance]
instance instIsNoetherianRing_henselianLocalRing_genericPoint (Z : PrimeDivisor X) :
    IsNoetherianRing (henselianLocalRing X Z.genericPoint) :=
  let _ := h_locallyNoetherian
  sorry

/-- Lemma 72.6.3 (3): let `Z ⊂ X` be a prime divisor with generic point
`ξ = Z.genericPoint`. Then `ringKrullDim (henselianLocalRing X ξ) = 1`. -/
@[stacks 0ENK]
theorem ringKrullDim_henselianLocalRing_genericPoint (Z : PrimeDivisor X) :
    ringKrullDim (henselianLocalRing X Z.genericPoint) = 1 :=
  sorry

/-- The henselian local ring at the generic point of a prime divisor is reduced,
Noetherian, and of Krull dimension one. -/
theorem henselianLocalRing_genericPoint_spec (Z : PrimeDivisor X) :
    _root_.IsReduced (henselianLocalRing X Z.genericPoint) ∧
      IsNoetherianRing (henselianLocalRing X Z.genericPoint) ∧
      ringKrullDim (henselianLocalRing X Z.genericPoint) = 1 :=
  sorry

/-- The henselian local ring at the generic point of a prime divisor has Krull
dimension at most one. -/
instance instKrullDimLE_one_henselianLocalRing_genericPoint (Z : PrimeDivisor X) :
    Ring.KrullDimLE 1 (henselianLocalRing X Z.genericPoint) :=
  let _ := h_locallyNoetherian
  sorry

/-- Lemma 72.6.3 (4): the canonical ring map `RationalFunction X ⟶
FractionRing (henselianLocalRing X ξ)` from the function field `R(X)` into
`Q(O_{X, ξ}^h)` at the generic point `ξ = Z.genericPoint` of a prime divisor
`Z ⊂ X`. -/
@[stacks 0ENK]
def functionFieldToHenselianFraction (Z : PrimeDivisor X) :
    RationalFunction X →+* FractionRing (henselianLocalRing X Z.genericPoint) :=
  let U := Classical.choose (exists_elementary_sectionsFractions_bijective Z)
  let hU := Classical.choose_spec (exists_elementary_sectionsFractions_bijective Z)
  (Localization.totalQuotientMap (henselianLocalRing.ι X Z.genericPoint U)
      (henselianLocalRing.ι_maps_nonZeroDivisors U)).comp
    ((neighbourhoodFractionsEquiv U hU).symm.toRingHom.comp
      (rationalFunctionComap (preservesDenseOpens_of_elementary U)))

/-- Lemma 72.6.3 (5): the canonical map `R(X) ⟶ Q(O_{X, ξ}^h)` is injective. -/
@[stacks 0ENK]
theorem functionFieldToHenselianFraction_injective (Z : PrimeDivisor X) :
    Function.Injective (functionFieldToHenselianFraction Z) :=
  sorry

/-- On any elementary étale neighbourhood where `R(U)` identifies with
`Q(Γ(U, ⊤))`, the canonical map is pullback of rational functions followed by
that identification and the total-quotient map of `henselianLocalRing.ι`. -/
theorem functionFieldToHenselianFraction_spec (Z : PrimeDivisor X)
    (U : EtaleNeighborhood.Elementary X Z.genericPoint)
    (hU : Function.Bijective (sectionsFractionsToRationalFunction U.obj.toOver)) :
    functionFieldToHenselianFraction Z =
      (Localization.totalQuotientMap (henselianLocalRing.ι X Z.genericPoint U)
          (henselianLocalRing.ι_maps_nonZeroDivisors U)).comp
        ((neighbourhoodFractionsEquiv U hU).symm.toRingHom.comp
          (rationalFunctionComap (preservesDenseOpens_of_elementary U))) :=
  sorry

/-- The canonical comparison associated to an integral closed subspace of
codimension one, recovered from `PrimeDivisor.ofSubspace`. -/
def functionFieldToHenselianFraction_ofSubspace (Z : ClosedSubspace X)
    [IsIntegral Z.X]
    (h_coheight : Order.coheight (ClosedSubspace.irreducibleClosed Z) = 1) :
    RationalFunction X →+* FractionRing
      (henselianLocalRing X (PrimeDivisor.ofSubspace X Z h_coheight).genericPoint) :=
  functionFieldToHenselianFraction (PrimeDivisor.ofSubspace X Z h_coheight)

/-- The closed-subspace comparison is the PrimeDivisor comparison of
`PrimeDivisor.ofSubspace`. -/
theorem functionFieldToHenselianFraction_ofSubspace_eq (Z : ClosedSubspace X)
    [IsIntegral Z.X]
    (h_coheight : Order.coheight (ClosedSubspace.irreducibleClosed Z) = 1) :
    functionFieldToHenselianFraction_ofSubspace Z h_coheight =
      functionFieldToHenselianFraction (PrimeDivisor.ofSubspace X Z h_coheight) :=
  sorry

/-- For an integral closed subspace, `localRingDimAt ξ = 1` at a generic point
`ξ` is coheight one of the associated irreducible closed support, so
`PrimeDivisor.ofSubspace` applies. -/
theorem functionFieldToHenselianFraction_ofSubspace_coheight (Z : ClosedSubspace X)
    [IsIntegral Z.X] {ξ : Points X} (hξ : IsGenericPoint ξ Z.pointsSet)
    (hcodim : localRingDimAt ξ = 1) :
    Order.coheight (ClosedSubspace.irreducibleClosed Z) = 1 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
