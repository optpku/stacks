/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.BaseChange.Bijective
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open scoped TensorProduct

universe u v x y

noncomputable section

namespace Ring.DirectLimit.Algebra.Approximation

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S}

/-
The ring approximation and the module system are intentionally separate.  The
former carries only the directed ring data; this structure adds the module
maps and their base-change laws without imposing finite type hypotheses.
-/
set_option linter.checkUnivs false in
/-
The `let`-bound algebra, restriction-of-scalars, and scalar-tower instances in
the base-change fields are induced by a chosen transition map.  They are not
canonical structures on the underlying rings, so keeping them local avoids
ambiguous global typeclass search; `ModuleSystem.BaseChange` packages the
resulting maps for downstream use.
-/
/-- A directed module system over a chosen ring-hom approximation.

The stage and limiting module maps are primitive data.  Finiteness and flatness
are separate predicates, so the same system can be reused for arbitrary
filtered-colimit arguments rather than only finite-type approximations. -/
@[stacks 02JO "directed module system"]
structure ModuleSystem (f : R →+* S) (M : Type x) [AddCommGroup M] [_root_.Module S M]
    extends Hom f where
  /-- Ring-stage base-change maps are bijective. -/
  stageBaseChange_bijective : toHom.baseChange_bijective
  /-- The module at each target stage. -/
  moduleStage : index → Type y
  /-- The additive structure on every stage module. -/
  moduleStage_addCommGroup : ∀ i, AddCommGroup (moduleStage i)
  /-- The target-stage module structure on every stage module. -/
  moduleStage_module : ∀ i, _root_.Module (target i) (moduleStage i)
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
  /-- The stage module is the base change of the earlier stage module. -/
  transitionBaseChange_spec :
    ∀ {i j} (h : i ≤ j),
      let _ : _root_.Module (target i) (moduleStage i) :=
        moduleStage_module i
      let _ : Algebra (target i) (target j) := (targetMap i j h).toAlgebra
      let _ : _root_.Module (target i) (moduleStage j) :=
        _root_.Module.compHom (moduleStage j) (targetMap i j h)
      let _ : IsScalarTower (target i) (target j) (moduleStage j) :=
        RestrictScalars.isScalarTower (target i) (target j) (moduleStage j)
      IsBaseChange (target j) (moduleMap h)
  /-- The limiting module is the base change of each stage module. -/
  finalBaseChange_spec :
    ∀ i,
      let _ : _root_.Module (target i) (moduleStage i) :=
        moduleStage_module i
      let _ : Algebra (target i) S := (toHom.targetToLimit i).toAlgebra
      let _ : _root_.Module (target i) M :=
        _root_.Module.compHom M (toHom.targetToLimit i)
      let _ : IsScalarTower (target i) S M :=
        RestrictScalars.isScalarTower (target i) S M
      IsBaseChange S (moduleToLimit i)

/- The generic system owns the canonical stage instances.  The finite-module
specialization keeps lower-priority compatibility projections, so a carrier
viewed through `A.toSystem` does not face two equally preferred candidates. -/
attribute [instance 1000] ModuleSystem.moduleStage_addCommGroup
attribute [instance 1000] ModuleSystem.moduleStage_module
attribute [simp] ModuleSystem.moduleMap_id ModuleSystem.moduleMap_comp
  ModuleSystem.moduleToLimit_comp

namespace ModuleSystem

variable {M : Type x} [AddCommGroup M] [_root_.Module S M]

/-- The source-stage scalar action on a module-system stage. -/
@[stacks 02JO "directed module system"]
abbrev sourceModule (A : ModuleSystem f M) (i : A.index) :
    _root_.Module (A.source i) (A.moduleStage i) :=
  _root_.Module.compHom (A.moduleStage i) (A.map i)

/-- The restriction-of-scalars action on a later stage module induced by a
transition map.  The transition is part of the argument, so this action is a
named map-local owner rather than a global instance. -/
@[stacks 02JO "directed module system"]
abbrev transitionModule (A : ModuleSystem f M)
    {i j : A.index} (h : i ≤ j) :
    _root_.Module (A.target i) (A.moduleStage j) :=
  _root_.Module.compHom (A.moduleStage j) (A.targetMap i j h)

/-- The target-stage scalar action on the limiting module. -/
@[stacks 02JO "directed module system"]
abbrev targetModule (A : ModuleSystem f M) (i : A.index) :
    _root_.Module (A.target i) M :=
  _root_.Module.compHom M (A.targetToLimit i)

/-- The stage-module finiteness condition for a directed module system.
This weaker predicate is the correct layer for finite-module models; it is
separate from `hasFinitePresentation` because finite and finitely presented
modules coincide only under additional hypotheses such as Noetherianity. -/
@[stacks 02JO "finite directed module system"]
def hasFinite (A : ModuleSystem f M) : Prop :=
  ∀ i, _root_.Module.Finite (A.target i) (A.moduleStage i)

/-- Read the finiteness of one stage module. -/
@[stacks 02JO "finite directed module system"]
theorem moduleStage_finite (A : ModuleSystem f M)
    (hA : A.hasFinite) (i : A.index) :
    _root_.Module.Finite (A.target i) (A.moduleStage i) := hA i

/-- The stage map and stage module finite-presentation conditions for a module
system.  This is the layer used by the finitely presented directed models in
Lemma 10.168.1 (2) and (3); it is separate from `hasFinite`, which is enough
for finite-module models. -/
@[stacks 02JO "finite-presentation directed module system"]
def hasFinitePresentation (A : ModuleSystem f M) : Prop :=
  (∀ i, (A.map i).FinitePresentation) ∧
    (∀ i, _root_.Module.FinitePresentation (A.target i) (A.moduleStage i))

/-- The finite-presentation property of a stage map. -/
@[stacks 02JO "finite-presentation directed module system"]
theorem map_finitePresentation (A : ModuleSystem f M)
    (hA : A.hasFinitePresentation) (i : A.index) :
    (A.map i).FinitePresentation := hA.1 i

/-- The finite-presentation property of a stage module. -/
@[stacks 02JO "finite-presentation directed module system"]
theorem moduleStage_finitePresentation (A : ModuleSystem f M)
    (hA : A.hasFinitePresentation) (i : A.index) :
    _root_.Module.FinitePresentation (A.target i) (A.moduleStage i) := hA.2 i

end ModuleSystem

end Ring.DirectLimit.Algebra.Approximation
