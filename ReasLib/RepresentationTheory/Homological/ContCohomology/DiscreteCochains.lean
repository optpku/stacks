/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Definition

@[expose] public section

universe u v

open CategoryTheory

namespace CategoryTheory.Action.ModuleCat.DiscreteModuleCat

section Representation

variable {R : Type u} {G : Type v} [Ring R] [Group G]
variable [TopologicalSpace R] [DiscreteTopology R]
variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Each group element acts by a continuous linear map on the discrete module carrier. -/
noncomputable def actionContinuousLinearMap (X : DiscreteModuleCat R G) (g : G) :
    -- Local instance justification (defeq pin): the continuous linear map uses the discrete carrier topology.
    letI : TopologicalSpace X.obj.V := ⊥
    X.obj.V →L[R] X.obj.V :=
  -- Local instance justification (defeq pin): the map must have the discrete topology fixed in its codomain.
  letI : TopologicalSpace X.obj.V := ⊥
  -- Local instance justification (proof-local temporary data): continuity of the original linear map follows from the discrete domain.
  letI : DiscreteTopology X.obj.V := ⟨rfl⟩
  { toLinearMap := (X.obj.ρ g).hom
    cont := continuous_of_discreteTopology }

/-- The identity group element acts as the identity continuous linear map. -/
theorem actionContinuousLinearMap_one (X : DiscreteModuleCat R G) :
    actionContinuousLinearMap X 1 = 1 := sorry

/-- Multiplication of group elements corresponds to composition of their continuous linear maps. -/
theorem actionContinuousLinearMap_mul (X : DiscreteModuleCat R G) (g h : G) :
    actionContinuousLinearMap X (g * h) =
      actionContinuousLinearMap X g * actionContinuousLinearMap X h := sorry

/-- A discrete continuous module determines a topological representation with its original action. -/
noncomputable def toTopRepOf (X : DiscreteModuleCat R G) : TopRep.{max u v} R G :=
  -- Local instance justification (defeq pin): `TopRep.of` must use the topology of `actionContinuousLinearMap`.
  letI : TopologicalSpace X.obj.V := ⊥
  -- Local instance justification (proof-local temporary data): the pinned carrier topology is discrete.
  letI : DiscreteTopology X.obj.V := ⟨rfl⟩
  -- Local instance justification (proof-local temporary data): the discrete carrier is a topological additive group.
  letI : IsTopologicalAddGroup X.obj.V := topologicalAddGroup_of_discreteTopology
  let moduleSmul : SMul R X.obj.V := ⟨(inferInstance : Module R X.obj.V).smul⟩
  -- Local instance justification (proof-local temporary data): both coefficient and carrier topologies are discrete.
  letI : @ContinuousSMul R X.obj.V moduleSmul _ _ :=
    @ContinuousSMul.mk R X.obj.V moduleSmul _ _ continuous_of_discreteTopology
  let action : G →* X.obj.V →L[R] X.obj.V :=
    { toFun := actionContinuousLinearMap X
      map_one' := actionContinuousLinearMap_one X
      map_mul' := actionContinuousLinearMap_mul X }
  TopRep.of (ContRepresentation.ofMonoidHom action)

/-- The carrier of the topological representation is the original discrete module carrier. -/
theorem toTopRepOf_V (X : DiscreteModuleCat R G) :
    (toTopRepOf X).V = X.obj.V := sorry

end Representation

/-- An integer-valued discrete continuous module determines a topological representation. -/
noncomputable def toTopRep (G : Type v) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (X : DiscreteModuleCat ℤ G) : TopRep.{v} ℤ G :=
  toTopRepOf X

/-- Homogeneous continuous cochains define a cohomology object for a discrete continuous module. -/
noncomputable def continuousCohomology (G : Type v) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (M : DiscreteModuleCat ℤ G) (n : ℕ) : TopModuleCat.{v} ℤ :=
  _root_.continuousCohomology n (toTopRep G M)

/-- Discrete-module cochain cohomology is homogeneous continuous-cochain cohomology of its representation. -/
theorem continuousCohomology_def (G : Type v) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (M : DiscreteModuleCat ℤ G) (n : ℕ) :
    continuousCohomology G M n =
      _root_.continuousCohomology n (toTopRep G M) := sorry

end CategoryTheory.Action.ModuleCat.DiscreteModuleCat
