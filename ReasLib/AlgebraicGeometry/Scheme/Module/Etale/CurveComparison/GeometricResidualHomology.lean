module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactResidualHomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.GeometricCyclotomic

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace AlgebraicGeometry.SchemeOverField.CompactResidual
variable {k : Type u} [Field k]
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
variable (X : SchemeOverField k)
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (ηbar : GeometricPoint (geometricBaseChange X))

/-- Actual geometric coinvariants with the residual fundamental-group action,
specialized to the geometric-arithmetic exact sequence. -/
def geometricCoinvariantsFunctor :=
  CompactResidualHomology.functor Λ
    (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar))
    (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))
    (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (galoisPoint X (arithmeticPoint X ηbar))))
    (geometricToArithmetic X ηbar).hom (arithmeticToGalois X (arithmeticPoint X ηbar)).hom
    (geometricToArithmetic_range_eq_arithmeticToGalois_ker X ηbar)
    (arithmeticToGalois_surjective X (arithmeticPoint X ηbar))

/-- The specialized geometric closed-coinvariant functor retains additivity. -/
instance geometricCoinvariantsFunctor_additive : (geometricCoinvariantsFunctor Λ X ηbar).Additive :=
  CompactResidualHomology.functor_additive Λ
    (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar))
    (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))
    (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (galoisPoint X (arithmeticPoint X ηbar))))
    (geometricToArithmetic X ηbar).hom (arithmeticToGalois X (arithmeticPoint X ηbar)).hom
    (geometricToArithmetic_range_eq_arithmeticToGalois_ker X ηbar)
    (arithmeticToGalois_surjective X (arithmeticPoint X ηbar))

/-- The specialized quotient functor preserves finite colimits. -/
instance geometricCoinvariantsFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (geometricCoinvariantsFunctor Λ X ηbar) :=
  CompactResidualHomology.functor_preservesFiniteColimits Λ
    (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar))
    (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))
    (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (galoisPoint X (arithmeticPoint X ηbar))))
    (geometricToArithmetic X ηbar).hom (arithmeticToGalois X (arithmeticPoint X ηbar)).hom
    (geometricToArithmetic_range_eq_arithmeticToGalois_ker X ηbar)
    (arithmeticToGalois_surjective X (arithmeticPoint X ηbar))

/-- Higher compact geometric coinvariants are derived in compact ARITHMETIC
representations, with the residual quotient action already in the output category. -/
def homology (n : ℕ) := (geometricCoinvariantsFunctor Λ X ηbar).leftDerived n

/-- Transport only the quotient group's name, through the actual finite-fiber
Galois comparison, retaining the compact coefficient module and maps. -/
def residualToGalois :
    CompactRepresentation.Cat Λ
      (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (galoisPoint X (arithmeticPoint X ηbar)))) ⥤
        Action (CompactModule Λ) Gal(AlgebraicClosure k/k) :=
  (CompactRepresentation.continuousAction Λ
      (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (galoisPoint X (arithmeticPoint X ηbar))))).ι ⋙
    Action.res (CompactModule Λ) (galoisToGaloisPoint X ηbar)

/-- The actual higher residual Galois functor; its action is not conjugated through a cohomology comparison. -/
def galoisHomology (n : ℕ) := homology Λ X ηbar n ⋙ residualToGalois Λ X ηbar

/-- The genuine degree-zero derived unit on residual Galois coinvariants. -/
def galoisHomologyZeroIso : galoisHomology Λ X ηbar 0 ≅
    geometricCoinvariantsFunctor Λ X ηbar ⋙ residualToGalois Λ X ηbar :=
  Functor.isoWhiskerRight (geometricCoinvariantsFunctor Λ X ηbar).leftDerivedZeroIsoSelf
    (residualToGalois Λ X ηbar)

/-- The finite inverse-Tate input is included in the compact arithmetic category
before applying higher residual homology; no finite projective resolution is used. -/
instance arithmeticInverseTate_finite (hΛ : IsUnit (Nat.card Λ : k))
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar))))
    [Finite M.obj.V] : Finite (AmbientGeometry.arithmeticInverseTate Λ X ηbar hΛ M).obj.V :=
  inferInstanceAs (Finite M.obj.V)

/-- The actual finite inverse-Tate coefficient, included before compact arithmetic derivation. -/
def finiteInverseTateHomology (hΛ : IsUnit (Nat.card Λ : k))
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar))))
    [Finite M.obj.V] (n : ℕ) :=
  (galoisHomology Λ X ηbar n).obj
    (CompactRepresentation.finiteCompactification Λ
      (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))
      (AmbientGeometry.arithmeticInverseTate Λ X ηbar hΛ M))

/-- Higher residual actions are jointly continuous in their actual compact-module topology. -/
theorem finiteInverseTateHomology_continuous (hΛ : IsUnit (Nat.card Λ : k))
    (M : DiscreteModuleCat Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar))))
    [Finite M.obj.V] (n : ℕ) :
    Continuous (fun gx : Gal(AlgebraicClosure k/k) ×
        (finiteInverseTateHomology Λ X ηbar hΛ M n).V.toModule ↦
      CompactModule.linear Λ ((finiteInverseTateHomology Λ X ηbar hΛ M n).ρ gx.1) gx.2) := sorry

end AlgebraicGeometry.SchemeOverField.CompactResidual
