module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.ChartPullback
public import ReasLib.AlgebraicGeometry.Scheme.RationalFunction.AffineFraction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian.EtaleChart
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.HenselianLocalRing.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood.Decent
public import ReasLib.RingTheory.Localization.TotalQuotient

/-! # Rational functions in henselian total quotient rings -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The coprojection from an affine elementary étale neighbourhood to the henselian
local ring preserves nonzerodivisors. -/
theorem henselianLocalRing.ι_maps_nonZeroDivisors {X : AlgebraicSpace S} [IsDecent X]
    {x : Points X} (U : EtaleNeighborhood.Elementary X x) [IsAffine U.obj.scheme] :
    nonZeroDivisors Γ((EtaleNeighborhood.Elementary.toScheme X x).obj U, ⊤) ≤
      Submonoid.comap (henselianLocalRing.ι X x U)
        (nonZeroDivisors (henselianLocalRing X x)) :=
  sorry

variable {X : AlgebraicSpace S} [IsLocallyNoetherian X] [IsIntegral X]

/-- Evaluate rational functions in the henselian total quotient ring through a supplied
affine elementary étale neighbourhood, using its reduced Noetherian total quotient ring. -/
def rationalFunctionHenselianChartMap (x : Points X)
    (U : EtaleNeighborhood.Elementary X x) [IsAffine U.obj.scheme] :
    RationalFunction X →+* FractionRing (henselianLocalRing X x) := by
  have hEtale : Etale U.obj.hom := (EtaleNeighborhood.spec U.obj).1
  have hNoetherian : AlgebraicGeometry.IsLocallyNoetherian U.obj.scheme :=
    @isLocallyNoetherian_left_of_etaleChart _ X inferInstance U.obj.toOver U.obj.hom hEtale
  have hReduced : AlgebraicGeometry.IsReduced U.obj.scheme :=
    (isReduced_iff_forallEtale X).mp inferInstance U.obj.toOver U.obj.hom
      (by
        have h : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf
            (𝟙 (yoneda.obj U.obj.toOver) ≫ U.obj.hom) :=
          hEtale.of_etale (𝟙 _) (ofOver_id_presheaf_etale U.obj.toOver)
        rw [Category.id_comp] at h
        exact h)
  exact (Localization.totalQuotientMap (henselianLocalRing.ι X x U)
      (henselianLocalRing.ι_maps_nonZeroDivisors U)).comp
    ((@Scheme.RationalFunction.toTotalQuotient U.obj.scheme inferInstance
        hNoetherian hReduced).comp
      (@RationalFunctionChart.map _ X U.obj.toOver U.obj.hom hEtale))

/-- A henselian fraction is the value of a rational function if it agrees with the
explicit comparison on every affine elementary étale neighbourhood. -/
def IsHenselianFractionValue (x : Points X) (f : RationalFunction X)
    (a : FractionRing (henselianLocalRing X x)) : Prop :=
  ∀ (U : EtaleNeighborhood.Elementary X x) [IsAffine U.obj.scheme],
    a = rationalFunctionHenselianChartMap x U f

/-- Every rational function has a unique value agreeing with all affine elementary
étale neighbourhood comparisons in the henselian total quotient ring. -/
theorem existsUnique_henselianFractionValue (x : Points X) (f : RationalFunction X) :
    ∃! a : FractionRing (henselianLocalRing X x), IsHenselianFractionValue x f a :=
  sorry

/-- The canonical comparison from rational functions to the total quotient ring of the
henselian local ring, characterized by its values on affine elementary étale charts. -/
def rationalFunctionToHenselianFraction (x : Points X) :
    RationalFunction X →+* FractionRing (henselianLocalRing X x) := by
  let value : RationalFunction X → FractionRing (henselianLocalRing X x) :=
    fun f ↦ @Classical.epsilon (FractionRing (henselianLocalRing X x)) ⟨0⟩
      (IsHenselianFractionValue x f)
  have laws : value 1 = 1 ∧ (∀ a b, value (a * b) = value a * value b) ∧
      value 0 = 0 ∧ (∀ a b, value (a + b) = value a + value b) := by
    sorry
  exact
    { toFun := value
      map_one' := laws.1
      map_mul' := laws.2.1
      map_zero' := laws.2.2.1
      map_add' := laws.2.2.2 }

/-- The canonical henselian comparison agrees with the explicit composite through every
affine elementary étale neighbourhood. -/
theorem rationalFunctionToHenselianFraction_spec (x : Points X)
    (U : EtaleNeighborhood.Elementary X x) [IsAffine U.obj.scheme]
    (f : RationalFunction X) :
    rationalFunctionToHenselianFraction x f = rationalFunctionHenselianChartMap x U f :=
  sorry

/-- The canonical comparison embeds the function field into the henselian total quotient
ring at every point of a locally Noetherian integral algebraic space. -/
theorem rationalFunctionToHenselianFraction_injective (x : Points X) :
    Function.Injective (rationalFunctionToHenselianFraction x) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
