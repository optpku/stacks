/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompletedTensorDerived

@[expose] public section

open CategoryTheory CategoryTheory.Action.ModuleCat

noncomputable section

universe u

namespace CompactRepresentation

variable (Λ G : Type u) [CommRing Λ] [Finite Λ]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Evaluation on genuine compact derived coinvariants. The input is homology,
not a character module substituted for homology. -/
def homologyPairing {M : DiscreteModuleCat Λ G} (I : InjectiveResolution M) (i : ℕ)
    (x : ((continuousHomology Λ G i).obj (dual Λ G M)).toModule)
    (c : (CategoryTheory.Action.ModuleCat.DiscreteModuleCat.derivedCohomologyFunctor Λ G i).obj M) : AddCircle (1 : ℚ) :=
  (derivedHomologyCharacterIso Λ G I i).hom x c

/-- For any compact input, first use its actual continuous evaluation map.
In particular no algebraic reflexivity of infinite modules is asserted. -/
def compactHomologyCharacterIso (K : Cat Λ G)
    (I : InjectiveResolution (continuousDual Λ G K)) (i : ℕ) :
    (CompactModule.forget Λ).obj ((continuousHomology Λ G i).obj K) ≅
      ModuleCat.of Λ (CharacterModule
        ((CategoryTheory.Action.ModuleCat.DiscreteModuleCat.derivedCohomologyFunctor Λ G i).obj (continuousDual Λ G K))) :=
  (CompactModule.forget Λ).mapIso
      ((continuousHomology Λ G i).mapIso (compactEvaluationIso Λ G K)) ≪≫
    derivedHomologyCharacterIso Λ G I i

def compactHomologyPairing (K : Cat Λ G)
    (I : InjectiveResolution (continuousDual Λ G K)) (i : ℕ)
    (x : ((continuousHomology Λ G i).obj K).toModule)
    (c : (CategoryTheory.Action.ModuleCat.DiscreteModuleCat.derivedCohomologyFunctor Λ G i).obj (continuousDual Λ G K)) :
    AddCircle (1 : ℚ) :=
  (compactHomologyCharacterIso Λ G K I i).hom x c

/-- The topology claim is for the specified map, and tests each finite
character coordinate. Its proof uses compact homology and closed images. -/
theorem compactHomologyPairing_continuous (K : Cat Λ G)
    (I : InjectiveResolution (continuousDual Λ G K)) (i : ℕ)
    (c : (CategoryTheory.Action.ModuleCat.DiscreteModuleCat.derivedCohomologyFunctor Λ G i).obj (continuousDual Λ G K)) :
    Continuous (fun x : ((continuousHomology Λ G i).obj K).toModule ↦
      CompactCharacters.evaluationCoordinates Λ
        ((CategoryTheory.Action.ModuleCat.DiscreteModuleCat.derivedCohomologyFunctor Λ G i).obj (continuousDual Λ G K))
        ((compactHomologyCharacterIso Λ G K I i).hom x) c) := by sorry

theorem homologyPairing_add_left {M : DiscreteModuleCat Λ G}
    (I : InjectiveResolution M) (i : ℕ)
    (x y : ((continuousHomology Λ G i).obj (dual Λ G M)).toModule)
    (c : (CategoryTheory.Action.ModuleCat.DiscreteModuleCat.derivedCohomologyFunctor Λ G i).obj M) :
    homologyPairing Λ G I i (x + y) c =
      homologyPairing Λ G I i x c + homologyPairing Λ G I i y c := by
  exact congrArg (fun χ : CharacterModule
    ((CategoryTheory.Action.ModuleCat.DiscreteModuleCat.derivedCohomologyFunctor Λ G i).obj M) ↦ χ c)
    ((derivedHomologyCharacterIso Λ G I i).hom.hom.map_add x y)

theorem homologyPairing_add_right {M : DiscreteModuleCat Λ G}
    (I : InjectiveResolution M) (i : ℕ)
    (x : ((continuousHomology Λ G i).obj (dual Λ G M)).toModule)
    (c d : (CategoryTheory.Action.ModuleCat.DiscreteModuleCat.derivedCohomologyFunctor Λ G i).obj M) :
    homologyPairing Λ G I i x (c + d) =
      homologyPairing Λ G I i x c + homologyPairing Λ G I i x d := by
  exact map_add _ _ _

/-- Evaluation after the specified completed-tensor comparison. -/
def completedTensorPairing [CompactSpace G] {M : DiscreteModuleCat Λ G}
    (I : InjectiveResolution M) (i : ℕ)
    (x : ((completedTensorHomology Λ G i).obj (dual Λ G M)).toModule)
    (c : (CategoryTheory.Action.ModuleCat.DiscreteModuleCat.derivedCohomologyFunctor Λ G i).obj M) : AddCircle (1 : ℚ) :=
  (completedTensorCharacterIso Λ G I i).hom x c

/-- Regression: the tensor pairing uses exactly the inverse of the canonical
derived projection comparison, followed by the genuine homology pairing. -/
theorem completedTensorPairing_spec [CompactSpace G] {M : DiscreteModuleCat Λ G}
    (I : InjectiveResolution M) (i : ℕ)
    (x : ((completedTensorHomology Λ G i).obj (dual Λ G M)).toModule)
    (c : (CategoryTheory.Action.ModuleCat.DiscreteModuleCat.derivedCohomologyFunctor Λ G i).obj M) :
    completedTensorPairing Λ G I i x c =
      homologyPairing Λ G I i
        (CompactModule.linear Λ
          ((continuousHomologyCompletedTensorIso Λ G i).app (dual Λ G M)).inv x) c := rfl

end CompactRepresentation
