module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactModuleDuality
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.AmbientDiscreteCohomology

@[expose] public section

open CategoryTheory CategoryTheory.Action.ModuleCat Opposite

noncomputable section

universe u

namespace CompactRepresentation

variable (Λ G : Type u) [CommRing Λ] [Finite Λ]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The actual contragredient action on compact characters, g acting by
precomposition with g⁻¹. -/
def dualAction (M : DiscreteModuleCat Λ G) : Action (CompactModule Λ) G where
  V := CompactModule.ofCharacter Λ M.obj.V
  ρ :=
    { toFun := fun g ↦ CompactModule.dualMap Λ (M.obj.ρ g⁻¹)
      map_one' := by sorry
      map_mul' := by sorry }

theorem dualAction_continuous (M : DiscreteModuleCat Λ G) :
    continuousAction Λ G (dualAction Λ G M) := by sorry

def dual (M : DiscreteModuleCat Λ G) : Cat Λ G :=
  ⟨dualAction Λ G M, dualAction_continuous Λ G M⟩

def dualMap {M N : DiscreteModuleCat Λ G} (f : M ⟶ N) : dual Λ G N ⟶ dual Λ G M :=
  ObjectProperty.homMk
    { hom := CompactModule.dualMap Λ f.hom.hom
      comm := by sorry }

def dualFunctor : (DiscreteModuleCat Λ G)ᵒᵖ ⥤ Cat Λ G where
  obj M := dual Λ G M.unop
  map f := dualMap Λ G f.unop
  map_id := by sorry
  map_comp := by sorry

/-- Only continuous characters of a compact representation are made discrete. -/
def continuousDualAction (M : Cat Λ G) : Action (ModuleCat.{u} Λ) G where
  V := CompactModule.characterModule Λ M.obj.V
  ρ :=
    { toFun := fun g ↦ CompactModule.characterMap Λ (M.obj.ρ g⁻¹)
      map_one' := by sorry
      map_mul' := by sorry }

/-- A continuous character of a compact module has open stabilizer under
a jointly continuous action. Its image lies in the finite annihilator. -/
theorem continuousDualAction_open (M : Cat Λ G) :
    openStabilizer Λ G (continuousDualAction Λ G M) := by sorry

def continuousDual (M : Cat Λ G) : DiscreteModuleCat Λ G :=
  ⟨continuousDualAction Λ G M, continuousDualAction_open Λ G M⟩

def continuousDualMap {M N : Cat Λ G} (f : M ⟶ N) :
    continuousDual Λ G N ⟶ continuousDual Λ G M :=
  ObjectProperty.homMk
    { hom := CompactModule.characterMap Λ f.hom.hom
      comm := by sorry }

def continuousDualFunctor : (Cat Λ G)ᵒᵖ ⥤ DiscreteModuleCat Λ G where
  obj M := continuousDual Λ G M.unop
  map f := continuousDualMap Λ G f.unop
  map_id := by sorry
  map_comp := by sorry

/-- Evaluation in the discrete category, equivariant for the specified actions. -/
def discreteEvaluationIso (M : DiscreteModuleCat Λ G) :
    M ≅ continuousDual Λ G (dual Λ G M) where
  hom := ObjectProperty.homMk
    { hom := (CompactModule.discreteEvaluationIso Λ M.obj.V).hom
      comm := by sorry }
  inv := ObjectProperty.homMk
    { hom := (CompactModule.discreteEvaluationIso Λ M.obj.V).inv
      comm := by sorry }
  hom_inv_id := by sorry
  inv_hom_id := by sorry

/-- Compact double-dual evaluation uses continuous, not all algebraic, characters. -/
def compactEvaluationIso (M : Cat Λ G) : M ≅ dual Λ G (continuousDual Λ G M) where
  hom := ObjectProperty.homMk
    { hom := (CompactModule.compactEvaluationIso Λ M.obj.V).hom
      comm := by sorry }
  inv := ObjectProperty.homMk
    { hom := (CompactModule.compactEvaluationIso Λ M.obj.V).inv
      comm := by sorry }
  hom_inv_id := by sorry
  inv_hom_id := by sorry

/-- Actual compact/discrete Pontryagin anti-equivalence for finite coefficients. -/
def equivalence : (DiscreteModuleCat Λ G)ᵒᵖ ≌ Cat Λ G where
  functor := dualFunctor Λ G
  inverse := (continuousDualFunctor Λ G).rightOp
  unitIso := NatIso.ofComponents (fun M ↦ (discreteEvaluationIso Λ G M.unop).symm.op) (by sorry)
  counitIso := NatIso.ofComponents (fun M ↦ (compactEvaluationIso Λ G M).symm) (by sorry)
  functor_unitIso_comp := by sorry

end CompactRepresentation
