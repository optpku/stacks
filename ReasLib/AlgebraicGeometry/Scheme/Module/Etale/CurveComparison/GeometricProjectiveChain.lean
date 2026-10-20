module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommGeometricFiniteModel

@[expose] public section
open CategoryTheory CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe r g u

namespace FiniteQuotientProjectiveChain
variable (R : Type r) [Ring R]
variable (G : Type g) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (K : CochainComplex (DiscreteModuleCat R G) ℤ)
variable [Finite (K.X 0).obj.V] [Finite (K.X 1).obj.V] [Finite (K.X 2).obj.V]
variable [K.IsStrictlyGE 0] [K.IsStrictlyLE 2]

/-- Expose the already constructed compatible-pair/free chain before its
degree embedding; no new projective replacement is chosen. -/
def chain := ((FiniteQuotientComplexReplacement.realization R G K).mapHomologicalComplex
  (ComplexShape.down ℕ)).obj
    (FiniteProjectiveComplexReplacement.complex (FiniteQuotientComplexReplacement.algebra R G K)
      (FiniteQuotientComplexReplacement.algebraChain R G K))

theorem extend_eq : (chain R G K).extend CompactRepresentation.curveDegreeEmbedding =
    FiniteQuotientComplexReplacement.complex R G K := rfl
end FiniteQuotientProjectiveChain

namespace GeometricProjectiveChain
variable {k : Type u} [Field k]
variable (R : Type (u + 1)) [Ring R] [Finite R]
variable (X : SchemeOverField k) [Curve X] [Smooth X.hom] [GeometricallyConnected X.hom]
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (η : GeometricPoint (geometricBaseChange X))
variable [X.left.smallEtaleTopology.HasSheafCompose (NoncommFiniteCoefficient.modules R)]
variable [X.left.smallEtaleTopology.HasSheafCompose (NoncommIntrinsicDualTransport.modules R)]
variable [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u + 1} R)]
variable [∀ U : X.left.Etale, HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} R)]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Rᵐᵒᵖ)]
variable [∀ U : X.left.Etale, HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} Rᵐᵒᵖ)]
variable [HasWeakSheafify X.left.smallEtaleTopology
  (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card R)))]
variable [∀ U : X.left.Etale, HasWeakSheafify (X.left.smallEtaleTopology.over U)
  (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card R)))]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [EnoughInjectives (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Rᵐᵒᵖ))]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Rᵐᵒᵖ),
  (smallEtalePullback f).op.HasLeftKanExtension F]
variable (hR : IsUnit (Nat.card R : k))
variable (M : (finiteTypeDiscreteModule R
  (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X η)))).FullSubcategory)

def chain :=
  -- Local instance justification (proof-local temporary data): retain the three actual finite geometric homology groups.
  letI : Finite ((NoncommGeometricFiniteModel.ordinary R X η M).homology 0).obj.V :=
    NoncommGeometricFiniteModel.ordinary_homology_finite R X η hR M 0
  -- Local instance justification (proof-local temporary data): degree-one geometric cohomology is finite.
  letI : Finite ((NoncommGeometricFiniteModel.ordinary R X η M).homology 1).obj.V :=
    NoncommGeometricFiniteModel.ordinary_homology_finite R X η hR M 1
  -- Local instance justification (proof-local temporary data): degree-two geometric cohomology is finite.
  letI : Finite ((NoncommGeometricFiniteModel.ordinary R X η M).homology 2).obj.V :=
    NoncommGeometricFiniteModel.ordinary_homology_finite R X η hR M 2
  FiniteQuotientProjectiveChain.chain Rᵐᵒᵖ Gal(AlgebraicClosure k/k)
    (FiniteCurveProjectiveModel.finiteModel Rᵐᵒᵖ Gal(AlgebraicClosure k/k)
      (NoncommGeometricFiniteModel.ordinary R X η M))

/-- The same complex, definitionally, with the approved degree 2-i placement. -/
theorem extend_eq : (chain R X η hR M).extend CompactRepresentation.curveDegreeEmbedding =
    NoncommGeometricFiniteModel.projectiveCochain R X η hR M := rfl

/-- These are the same finite free-on-compatible-pairs terms, after coefficient restriction. -/
theorem term_finite (i : ℕ) : Finite ((chain R X η hR M).X i).obj.V := by sorry

/-- Projective only over the coefficient ring, never asserted projective in
the finite or all-discrete Galois representation category. -/
theorem term_projective (i : ℕ) : Module.Projective Rᵐᵒᵖ ((chain R X η hR M).X i).obj.V := by sorry

variable (P : Compactification.Of (Spec (CommRingCat.of k)) X)

def pulledChain := ((FieldGeometricAdjunction.pullback Rᵐᵒᵖ P.obj.right).mapHomologicalComplex
  (ComplexShape.down ℕ)).obj (chain R X η hR M)

/-- Canonical functor/degree-extension identification needed for the actual
global Hom arrow and the subsequent Koszul transpose. -/
def pulledIso : (pulledChain R X η hR M P).extend CompactRepresentation.curveDegreeEmbedding ≅
    ((FieldGeometricAdjunction.pullback Rᵐᵒᵖ P.obj.right).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (NoncommGeometricFiniteModel.projectiveCochain R X η hR M) :=
  (CompactRepresentation.curveDegreeEmbedding.mapAppIso
    (FieldGeometricAdjunction.pullback Rᵐᵒᵖ P.obj.right) (chain R X η hR M)).symm ≪≫
  eqToIso (congrArg
    ((FieldGeometricAdjunction.pullback Rᵐᵒᵖ P.obj.right).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (extend_eq R X η hR M))

end GeometricProjectiveChain
