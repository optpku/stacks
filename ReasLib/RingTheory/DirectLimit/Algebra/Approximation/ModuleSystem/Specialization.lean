module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Module.Core
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Module.Finiteness
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem.Core
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem.Finiteness
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u v x y

noncomputable section

namespace Ring.DirectLimit.Algebra.Approximation

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S} {M : Type x} [AddCommGroup M] [_root_.Module S M]

/-- Forget the finite-type fields of an approximation module and retain its
generic directed module-system structure. -/
@[stacks 00R1 "finite-type module-system specialization"]
def Module.toSystem (A : Module f M) : ModuleSystem f M where
  toHom := A.toHom
  stageBaseChange_bijective := A.stageBaseChange_bijective
  moduleStage := A.moduleStage
  moduleStage_addCommGroup := A.moduleStage_addCommGroup
  moduleStage_module := A.moduleStage_module
  moduleMap := A.moduleMap
  moduleMap_id := A.moduleMap_id
  moduleMap_comp := A.moduleMap_comp
  moduleToLimit := A.moduleToLimit
  moduleToLimit_comp := A.moduleToLimit_comp
  transitionBaseChange_spec := sorry
  finalBaseChange_spec := sorry

/-- The finite-type approximation module supplies a finite-stage predicate
without claiming that arbitrary finite modules are finitely presented. -/
@[stacks 00R1 "finite-type module-system specialization"]
theorem Module.toSystem_finite (A : Module f M) :
    (A.toSystem).hasFinite := sorry

/-- The finite-type approximation module supplies the stage
finite-presentation predicate required by the generic flatness theorem.  This
uses the Noetherian target-stage consequence of the finite-type approximation. -/
@[stacks 00R1 "finite-type module-system specialization"]
theorem Module.toSystem_finitePresentation (A : Module f M) :
    (A.toSystem).hasFinitePresentation := sorry

end Ring.DirectLimit.Algebra.Approximation
