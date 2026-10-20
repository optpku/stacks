module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.GeometricCharacterEndpoint
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace GeometricCharacterPairing
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


abbrev finiteComplex := NoncommGeometricFiniteModel.projectiveCochain R X η hR M
abbrev characterComplex := GeometricCharacterEndpoint.target R X η hR M
abbrev ordinaryComplex := NoncommGeometricFiniteModel.ordinary R X η M

/-- The specified finite-model quasi-isomorphism, on actual ordinary cohomology. -/
def ordinaryHomologyIso (i : ℤ) :
    (finiteComplex R X η hR M).homology i ≅ (ordinaryComplex R X η M).homology i :=
  -- Local instance justification (proof-local temporary data): the specified finite-model map is a quasi-isomorphism.
  letI := NoncommGeometricFiniteModel.projectiveMap_quasiIso R X η hR M
  asIso (HomologicalComplex.homologyMap (NoncommGeometricFiniteModel.projectiveMap R X η hR M) i)

/-- The quotient from cycles to the actual cohomology of discrete modules is surjective. -/
theorem ordinary_cycles_surjective (i : ℤ) :
    Function.Surjective ((finiteComplex R X η hR M).homologyπ i).hom.hom.hom := by sorry

/-- Choose representatives only through the actual surjective cycles quotient. -/
def ordinaryCycle (i : ℤ) (y : ((ordinaryComplex R X η M).homology i).obj.V) :
    ((finiteComplex R X η hR M).cycles i).obj.V :=
  Function.surjInv (ordinary_cycles_surjective R X η hR M i)
    ((ordinaryHomologyIso R X η hR M i).inv.hom.hom.hom y)

/-- The completed coefficient category has the usual surjective cycles quotient. -/
theorem character_cycles_surjective (i : ℤ) :
    Function.Surjective ((characterComplex R X η hR M).homologyπ i).hom :=
  (ModuleCat.epi_iff_surjective _).mp inferInstance

def characterCycle (i : ℤ) (x : (characterComplex R X η hR M).homology i) :
    (characterComplex R X η hR M).cycles i :=
  Function.surjInv (character_cycles_surjective R X η hR M i) x

/-- Evaluation of actual cycle representatives. Changing either representative
changes the value by zero, since the opposite representative is a cycle.
The second argument is the actual geometric intrinsic-dual cohomology. -/
def value (i : ℤ) (x : (characterComplex R X η hR M).homology (2 - i))
    (y : ((ordinaryComplex R X η M).homology i).obj.V) : AddCircle (1 : ℚ) :=
  (show ActualOppositeCharacter.Carrier
      ((finiteComplex R X η hR M).X (2 - (2 - i))).obj.V from
    ((characterComplex R X η hR M).iCycles (2 - i)).hom
      (characterCycle R X η hR M (2 - i) x))
      (((finiteComplex R X η hR M).XIsoOfEq (by omega : i = 2 - (2 - i))).hom.hom.hom.hom
        (((finiteComplex R X η hR M).iCycles i).hom.hom.hom (ordinaryCycle R X η hR M i y)))

/-- Actual character-valued evaluation on cohomology, not a chosen perfect pairing. -/
def characterMap (i : ℤ) : (characterComplex R X η hR M).homology (2 - i) →+
    CharacterModule (((ordinaryComplex R X η M).homology i).obj.V) where
  toFun x :=
    { toFun := value R X η hR M i x
      map_zero' := by sorry
      map_add' := by sorry }
  map_zero' := by sorry
  map_add' := by sorry

/-- Exact character duality and the specified finite-model quasi-isomorphism
make this evaluation perfect. It does not assume geometric duality. -/
theorem characterMap_bijective (i : ℤ) : Function.Bijective (characterMap R X η hR M i) := by sorry

end GeometricCharacterPairing
