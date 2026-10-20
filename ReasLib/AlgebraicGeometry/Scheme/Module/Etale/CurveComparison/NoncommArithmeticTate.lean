module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommFiniteCoefficient
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommDerivedTensor

@[expose] public section
open CategoryTheory CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace NoncommArithmeticTate
variable {k : Type u} [Field k]
variable (R : Type (u + 1)) [Ring R] [Finite R]
variable (X : SchemeOverField k)
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (η : GeometricPoint (geometricBaseChange X))
variable (hR : IsUnit (Nat.card R : k))

include hR in
/-- The actual roots-of-unity cardinality; only the integer cardinality,
not commutativity of R, occurs in this geometric fact. -/
theorem roots_card : Nat.card {x // x ∈ rootsOfUnity (Nat.card R) (AlgebraicClosure k)} =
    Nat.card R := by sorry

/-- The central arithmetic cyclotomic character obtained from the actual
modular cyclotomic character and the integer-quotient map into R. -/
def cyclotomic : Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X η)) →* Rˣ :=
  (Units.map (NoncommFiniteCoefficient.zmodHom R).toMonoidHom).comp
    ((modularCyclotomicCharacter (AlgebraicClosure k) (roots_card R hR)).comp
      ((AlgebraicGeometry.Scheme.Etale.galoisToRingAut k).comp
        (AmbientGeometry.arithmeticGaloisQuotient X η)))

/-- This finite cyclotomic character, unlike an arbitrary infinite module
action, has open kernel. -/
theorem cyclotomic_open : IsOpen ((cyclotomic R X η hR).ker :
    Set (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X η)))) := by sorry

/-- The inverse character values are central, so the twisted action remains R-linear. -/
theorem inverse_cyclotomic_commute
    (g : Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X η))) (r : R) :
    (((cyclotomic R X η hR g)⁻¹ : Rˣ) : R) * r =
      r * (((cyclotomic R X η hR g)⁻¹ : Rˣ) : R) := by sorry

/-- Actual inverse Tate action, valid for all discrete left R representations. -/
def inverseAction
    (M : DiscreteModuleCat R (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X η)))) :
    Action (ModuleCat.{u + 1} R) (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X η))) where
  V := M.obj.V
  ρ := { toFun := fun g ↦ ModuleCat.ofHom
          { toFun := fun m ↦ (((cyclotomic R X η hR g)⁻¹ : Rˣ) : R) • (M.obj.ρ g).hom m
            map_add' := by intros; simp
            map_smul' := by sorry }
         map_one' := by sorry
         map_mul' := by sorry }

/-- Intersect the original vector stabilizer with this finite character kernel. -/
theorem inverseAction_open
    (M : DiscreteModuleCat R (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X η)))) :
    openStabilizer R (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X η)))
      (inverseAction R X η hR M) := by sorry

/-- The twist keeps the actual coefficient carrier and changes only its specified action. -/
def inverseTwist
    (M : DiscreteModuleCat R (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X η)))) :
    DiscreteModuleCat R (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X η))) :=
  ⟨inverseAction R X η hR M, inverseAction_open R X η hR M⟩

variable (M : (finiteTypeDiscreteModule R
  (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X η)))).FullSubcategory)

/-- Finite-type over a finite ring gives a finite underlying coefficient. -/
theorem input_finite : Finite M.obj.obj.V := by
  -- Local instance justification (defeq pin): expose the finite-type property stored by the actual input object.
  letI : Module.Finite R M.obj.obj.V := M.property
  infer_instance

/-- Canonical double-opposite restriction changes handedness twice and
retains the original finite carrier. -/
def doubleOppositeAction :=
  ((ModuleCat.restrictScalars (RingEquiv.opOp R).symm.toRingHom).mapAction
    (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X η)))).obj
      (inverseTwist R X η hR M.obj).obj

/-- The finite inverse-Tate coefficient with its actual discrete compact topology. -/
def compactCoefficient : NoncommCompactModule Rᵐᵒᵖᵐᵒᵖ :=
        { toModule := (doubleOppositeAction R X η hR M).V
          topology := ⊥
          compact := by
            -- Local instance justification (defeq pin): the double-opposite restriction has the same finite carrier as M.
            letI : Finite (doubleOppositeAction R X η hR M).V := input_finite R X η M
            exact inferInstance
          t2 := by sorry
          topologicalAdd := by sorry
          scalarContinuous := by sorry }

/-- The compact inverse-Tate input used by the noncommutative projective
resolution. Double-opposite coefficients are removed at the completed endpoint. -/
def compactInput : NoncommCompactRepresentation.Cat Rᵐᵒᵖᵐᵒᵖ
    (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X η))) :=
  ⟨{ V := compactCoefficient R X η hR M
     ρ := { toFun := fun g ↦
              { toLinearMap := ((doubleOppositeAction R X η hR M).ρ g).hom
                cont := by sorry }
            map_one' := by sorry
            map_mul' := by sorry } }, by sorry⟩

end NoncommArithmeticTate
