/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.BaseChange.Bijective
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Directed finite-module approximation data

This leaf owns the concrete finite-module system attached to an approximation.
Its transition and limiting base-change maps are defined in the companion
`Approximation.Module.BaseChange` leaf.
-/

@[expose] public section

open scoped TensorProduct

universe u v w x y

noncomputable section

namespace Ring.DirectLimit.Algebra.Approximation

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-
The carrier universe of a stage module is independent of the universes of the
source and target rings.  It occurs only in the module-system fields, so the
universe linter cannot distinguish this required generality from a redundant
`max` expression.
-/
set_option linter.checkUnivs false in
/-- A finite-module system over a finite-type directed approximation of a
ring homomorphism.  Its transition and limiting maps are required to become
isomorphisms after the indicated scalar extensions. -/
@[stacks 00R1 "finite module approximation"]
structure Module (f : R →+* S) (M : Type x) [AddCommGroup M] [_root_.Module S M]
    extends FiniteType f where
  /-- Ring-stage base-change maps are bijective. -/
  stageBaseChange_bijective : toHom.baseChange_bijective
  /-- The module at each target stage. -/
  moduleStage : index → Type y
  /-- The additive structure on every stage module. -/
  moduleStage_addCommGroup : ∀ i, AddCommGroup (moduleStage i)
  /-- The target-stage module structure on every stage module. -/
  moduleStage_module : ∀ i, _root_.Module (target i) (moduleStage i)
  /-- Every stage module is finite over its target stage. -/
  moduleStage_finite : ∀ i, _root_.Module.Finite (target i) (moduleStage i)
  /-- The transition map between comparable stage modules. -/
  moduleMap :
    ∀ {i j} (h : i ≤ j),
      let _ : _root_.Module (target i) (moduleStage j) :=
        _root_.Module.compHom (moduleStage j) (targetMap i j h)
      moduleStage i →ₗ[target i] moduleStage j
  /-- The transition at one stage is the identity. -/
  moduleMap_id : ∀ i (m : moduleStage i), moduleMap le_rfl m = m
  /-- Stage-module transitions compose. -/
  moduleMap_comp :
    ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k) (m : moduleStage i),
      moduleMap hjk (moduleMap hij m) = moduleMap (hij.trans hjk) m
  /-- The map from a stage module to the limiting module. -/
  moduleToLimit :
    ∀ i,
      let _ : _root_.Module (target i) M :=
        _root_.Module.compHom M (toHom.targetToLimit i)
      moduleStage i →ₗ[target i] M
  /-- The maps to the limit are compatible with transitions. -/
  moduleToLimit_comp :
    ∀ {i j} (h : i ≤ j) (m : moduleStage i),
      moduleToLimit j (moduleMap h m) = moduleToLimit i m
  /-- Extension of a stage module along a target transition is bijective. -/
  transitionBaseChange_bijective :
    ∀ {i j} (h : i ≤ j),
      let _ : Algebra (target i) (target j) := (targetMap i j h).toAlgebra
      let _ : _root_.Module (target i) (moduleStage j) :=
        _root_.Module.compHom (moduleStage j) (targetMap i j h)
      let _ : IsScalarTower (target i) (target j) (moduleStage j) :=
        RestrictScalars.isScalarTower (target i) (target j) (moduleStage j)
      Function.Bijective
        (((moduleMap h).liftBaseChange (target j)) :
          target j ⊗[target i] moduleStage i →ₗ[target j] moduleStage j)
  /-- Extension of a stage module to the limiting target is bijective. -/
  finalBaseChange_bijective :
    ∀ i,
      let _ : Algebra (target i) S := (toHom.targetToLimit i).toAlgebra
      let _ : _root_.Module (target i) M :=
        _root_.Module.compHom M (toHom.targetToLimit i)
      let _ : IsScalarTower (target i) S M :=
        RestrictScalars.isScalarTower (target i) S M
      Function.Bijective
        (((moduleToLimit i).liftBaseChange S) :
          S ⊗[target i] moduleStage i →ₗ[S] M)

/- These projections preserve the historical `Module` API.  The generic
`ModuleSystem` projections are canonical and have higher priority when a
finite model is viewed through `toSystem`. -/
attribute [instance 900] Module.moduleStage_addCommGroup
attribute [instance 900] Module.moduleStage_module
attribute [instance] Module.moduleStage_finite
attribute [simp] Module.moduleMap_id Module.moduleMap_comp Module.moduleToLimit_comp

namespace Module

variable {f : R →+* S} {M : Type x} [AddCommGroup M] [_root_.Module S M]

end Module

end Ring.DirectLimit.Algebra.Approximation
