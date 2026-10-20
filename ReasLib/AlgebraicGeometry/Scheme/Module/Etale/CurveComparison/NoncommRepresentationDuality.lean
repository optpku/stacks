module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommCompactDuality
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Cohomology
public import Mathlib.CategoryTheory.Abelian.Transfer

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat Opposite
noncomputable section
universe u

namespace NoncommRepresentationDuality
variable (R G : Type u) [Ring R] [Finite R]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The compact character action is actual precomposition by g⁻¹. -/
def dualAction (M : DiscreteModuleCat R G) : Action (NoncommCompactModule Rᵐᵒᵖ) G where
  V := NoncommCompactCharacters.dual R M.obj.V
  ρ := { toFun := fun g ↦ NoncommCompactCharacters.map R M.obj.V (M.obj.ρ g⁻¹)
         map_one' := by sorry
         map_mul' := by sorry }

/-- Individual open stabilizers make the compact contragredient action jointly continuous. -/
theorem dualAction_continuous (M : DiscreteModuleCat R G) :
    NoncommCompactRepresentation.continuousAction Rᵐᵒᵖ G (dualAction R G M) := by sorry

/-- All discrete left modules dualize to compact right modules. -/
def dual (M : DiscreteModuleCat R G) : NoncommCompactRepresentation.Cat Rᵐᵒᵖ G :=
  ⟨dualAction R G M, dualAction_continuous R G M⟩

/-- The actual continuous equivariant character map. -/
def dualMap {M N : DiscreteModuleCat R G} (f : M ⟶ N) : dual R G N ⟶ dual R G M :=
  ObjectProperty.homMk
    { hom := NoncommCompactCharacters.map R M.obj.V f.hom.hom
      comm := fun _ ↦ by sorry }

/-- Contravariant compactification of characters, with coefficient handedness retained. -/
def dualFunctor : (DiscreteModuleCat R G)ᵒᵖ ⥤ NoncommCompactRepresentation.Cat Rᵐᵒᵖ G where
  obj M := dual R G M.unop
  map f := dualMap R G f.unop
  map_id := by sorry
  map_comp := by sorry

/-- Continuous right-module characters, returned to left R via the double opposite. -/
def inverseAction (M : NoncommCompactRepresentation.Cat Rᵐᵒᵖ G) :
    Action (ModuleCat.{u} R) G where
  V := NoncommCompactDuality.inverseDiscrete R M.obj.V
  ρ := { toFun := fun g ↦ (ModuleCat.restrictScalars (RingEquiv.opOp R).toRingHom).map
            (NoncommCompactDuality.characterMap Rᵐᵒᵖ (M.obj.ρ g⁻¹))
         map_one' := by sorry
         map_mul' := by sorry }

/-- Uniform continuity on the compact coefficient gives open stabilizers of
each continuous character. No open kernel for all characters is asserted. -/
theorem inverseAction_open (M : NoncommCompactRepresentation.Cat Rᵐᵒᵖ G) :
    openStabilizer R G (inverseAction R G M) := by sorry

/-- The actual all-discrete inverse representation. -/
def inverseDiscrete (M : NoncommCompactRepresentation.Cat Rᵐᵒᵖ G) : DiscreteModuleCat R G :=
  ⟨inverseAction R G M, inverseAction_open R G M⟩

/-- Actual precomposition on the continuous-character inverse. -/
def inverseMap {M N : NoncommCompactRepresentation.Cat Rᵐᵒᵖ G} (f : M ⟶ N) :
    inverseDiscrete R G N ⟶ inverseDiscrete R G M :=
  ObjectProperty.homMk
    { hom := (ModuleCat.restrictScalars (RingEquiv.opOp R).toRingHom).map
        (NoncommCompactDuality.characterMap Rᵐᵒᵖ f.hom.hom)
      comm := fun _ ↦ by sorry }

/-- The inverse contravariant functor on compact right representations. -/
def inverseFunctor : (NoncommCompactRepresentation.Cat Rᵐᵒᵖ G)ᵒᵖ ⥤ DiscreteModuleCat R G where
  obj M := inverseDiscrete R G M.unop
  map f := inverseMap R G f.unop
  map_id := by sorry
  map_comp := by sorry

/-- Actual evaluation unit, with equivariance as a law of that specified map. -/
def discreteEvaluationIso (M : DiscreteModuleCat R G) : M ≅ inverseDiscrete R G (dual R G M) :=
  ObjectProperty.isoMk _ (Action.mkIso
    (NoncommCompactDuality.discreteEvaluationIso R M.obj.V) (fun _ ↦ by sorry))

/-- Actual continuous evaluation counit, not an algebraic infinite bidual iso. -/
def compactEvaluationIso (M : NoncommCompactRepresentation.Cat Rᵐᵒᵖ G) :
    M ≅ dual R G (inverseDiscrete R G M) :=
  ObjectProperty.isoMk _ (Action.mkIso
    (NoncommCompactDuality.compactEvaluationIso R M.obj.V) (fun _ ↦ by sorry))

/-- The full noncommutative compact/discrete representation anti-equivalence. -/
def equivalence : (DiscreteModuleCat R G)ᵒᵖ ≌ NoncommCompactRepresentation.Cat Rᵐᵒᵖ G where
  functor := dualFunctor R G
  inverse := (inverseFunctor R G).rightOp
  unitIso := NatIso.ofComponents (fun M ↦ (discreteEvaluationIso R G M.unop).symm.op) (by sorry)
  counitIso := NatIso.ofComponents (fun M ↦ (compactEvaluationIso R G M).symm) (by sorry)
  functor_unitIso_comp := by sorry

instance compact_finiteProducts : HasFiniteProducts (NoncommCompactRepresentation.Cat Rᵐᵒᵖ G) := by sorry

instance inverse_isEquivalence : ((equivalence R G).inverse).IsEquivalence :=
  (equivalence R G).isEquivalence_inverse

/-- Transfer abelianness through the displayed continuous anti-equivalence. -/
instance compact_abelian : Abelian (NoncommCompactRepresentation.Cat Rᵐᵒᵖ G) :=
  abelianOfEquivalence (equivalence R G).inverse

/-- Compact duals of actual ambient injectives are projective. -/
theorem dual_projective (M : DiscreteModuleCat R G) [Injective M] :
    Projective (dual R G M) := by sorry

end NoncommRepresentationDuality
