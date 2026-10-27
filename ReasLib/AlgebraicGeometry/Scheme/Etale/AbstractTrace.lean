/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Algebra.Category.ProfiniteGrp.AbstractTrace
public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.FiniteFieldDegree
public import ReasLib.AlgebraicGeometry.Scheme.Etale.KPi1
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.AssociatedSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic

/-! # Étale cohomology and abstract trace formulas over finite fields -/

@[expose] public section
open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits
open CategoryTheory.Action.ModuleCat ProfiniteGrp ProfiniteGrp.ContinuousTrace
open scoped Ring
noncomputable section
universe u

namespace AlgebraicGeometry.SchemeOverField
variable {k : Type u} [Field k] [Fintype k] (X : SchemeOverField k)
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (η : GeometricPoint (geometricBaseChange X))

namespace EtaleTrace
variable {Λ : Type (u + 1)} [Ring Λ] [Finite Λ]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ),
  (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
variable [EnoughInjectives (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
variable (M : DiscreteModuleCat Λ
  (GeometricPoint.etaleFundamentalGroup X.left (arithmeticPoint X η)))
variable [Module.Finite Λ M.obj.V]

/-- Geometric cochains of the associated finite local system, forgetting residual action. -/
def cohomologyComplex : CochainComplex (ModuleCat.{u + 1} Λ) ℤ :=
  (((openStabilizer Λ Gal(AlgebraicClosure k/k)).ι ⋙
      Action.forget (ModuleCat.{u + 1} Λ) Gal(AlgebraicClosure k/k)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj
      (NoncommGeometricSource.arithmeticDiscreteCochain Λ X
        (associatedSheaf Λ (arithmeticPoint X η) ⟨M, (inferInstance : Module.Finite Λ M.obj.V)⟩))

/-- Geometric Frobenius acts degreewise by inverse arithmetic Frobenius on the cochains. -/
def frobeniusComplex : End (cohomologyComplex X η M) :=
  let C := NoncommGeometricSource.arithmeticDiscreteCochain Λ X
    (associatedSheaf Λ (arithmeticPoint X η) ⟨M, (inferInstance : Module.Finite Λ M.obj.V)⟩)
  { f := fun i ↦ (C.X i).obj.ρ (FiniteField.arithmeticFrobenius k)⁻¹
    comm' := sorry }

/-- Geometric cohomology is the localization of the associated local system's cochains. -/
def cohomology : DerivedCategory (ModuleCat.{u + 1} Λ) :=
  DerivedCategory.Q.obj (cohomologyComplex X η M)

/-- Geometric Frobenius on cohomology is the localization of its chain endomorphism. -/
def frobenius : End (cohomology X η M) :=
  DerivedCategory.Q.map (frobeniusComplex X η M)

/-- Geometric cohomology is computed by the specified geometric-sections complex. -/
theorem cohomology_def : cohomology X η M =
    DerivedCategory.Q.obj (cohomologyComplex X η M) := sorry

/-- The Frobenius endomorphism is the image of its specified cochain action. -/
theorem frobenius_def : frobenius X η M =
    DerivedCategory.Q.map (frobeniusComplex X η M) := sorry

/-- Finite projective local systems with invertible coefficient cardinality have
perfect geometric cohomology on smooth separated finite-type schemes. -/
theorem isPerfect_cohomology [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom]
    [Smooth X.hom] [Module.Projective Λ M.obj.V] (hunit : IsUnit (Nat.card Λ : k)) :
    DerivedCategory.IsPerfect (cohomology X η M) := sorry

/-- On a projective curve, the abstract divisor sum equals the cohomological
Frobenius trace without a power-of-cardinality factor. -/
theorem trace_eq_cohomology {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    [Curve X] [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom]
    (h_ne_P1 : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))
    (T : AbstractTraceData (DegreeExtension.ofEtaleFundamentalGroup X η))
    (hT : IsAbstractTraceFormula (DegreeExtension.ofEtaleFundamentalGroup X η) T)
    (hq : T.q = Fintype.card k) (hunit : IsUnit (T.q : Λ))
    [Module.Projective Λ M.obj.V] (hcoeff : IsUnit (Nat.card Λ : k)) (n : ℕ) (hn : 0 < n) :
    T.leftHandSum M n = (isPerfect_cohomology X η M hcoeff).traceNatural
      (frobenius X η M ^ n) := sorry

end EtaleTrace

/-- A smooth geometrically irreducible separated finite-type étale K(π, 1)
over a finite field has abstract trace data with integer card(k)^dim(X). -/
theorem hasAbstractTraceFormula_etaleFundamentalGroup
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom]
    [Smooth X.hom] [GeometricallyIrreducible X.hom] [IsEtaleKPi1 X η] :
    ∃ (d : ℕ) (T : AbstractTraceData (DegreeExtension.ofEtaleFundamentalGroup X η)),
      topologicalKrullDim X.left = (d : WithBot ℕ∞) ∧ T.q = Fintype.card k ^ d ∧
        IsAbstractTraceFormula (DegreeExtension.ofEtaleFundamentalGroup X η) T := sorry

/-- A smooth geometrically irreducible curve other than geometric P¹ has abstract
trace data with distinguished integer card(k). -/
theorem hasAbstractTraceFormula_etaleFundamentalGroup_curve
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    [Curve X] [Smooth X.hom] [GeometricallyIrreducible X.hom]
    (h_ne_P1 : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1)) :
    ∃ T : AbstractTraceData (DegreeExtension.ofEtaleFundamentalGroup X η),
      T.q = Fintype.card k ∧ IsAbstractTraceFormula (DegreeExtension.ofEtaleFundamentalGroup X η) T := sorry

end AlgebraicGeometry.SchemeOverField
