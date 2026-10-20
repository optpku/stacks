/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.CompleteDevissageAtAmbientPoint
public import ReasLib.AlgebraicGeometry.Scheme.Module.CompleteDevissage.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.OneStepDevissageAtAmbientPoint.BaseChange

/-!
# Base change of complete dévissages at ambient points

This module transports complete dévissages with distinguished ambient points across
affine pointed base changes that induce isomorphisms on residue fields.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.CompleteDevissageAtAmbientPoint

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S S' X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
  [h_f : LocallyOfFiniteType f] [h_Fqc : F.IsQuasicoherent]
  [h_Fft : F.IsFiniteType] {x : X}

section

variable (D : CompleteDevissageAtAmbientPoint f F x) (g : S' ⟶ S) (s' : S')
  (h_point : g s' = f x) [h_affine : IsAffine S']
  [h_residue : IsIso (g.residueFieldMap s')]
  (x' : (Limits.pullback f g : Scheme))
  (h_x_fst : pullback.fst f g x' = x)
  (h_x_snd : pullback.snd f g x' = s')
  (z' : ∀ k, (Limits.pullback (D.toCompleteDevissageOver.stage k).Z.hom g : Scheme))
  (h_z_fst : ∀ k, pullback.fst (D.toCompleteDevissageOver.stage k).Z.hom g (z' k) =
    D.z k)
  (h_z_snd : ∀ k, pullback.snd (D.toCompleteDevissageOver.stage k).Z.hom g (z' k) = s')
  (y' : ∀ k, (Limits.pullback (D.toCompleteDevissageOver.stage k).Y.hom g : Scheme))
  (h_y_fst : ∀ k, pullback.fst (D.toCompleteDevissageOver.stage k).Y.hom g (y' k) =
    D.y k)
  (h_y_snd : ∀ k, pullback.snd (D.toCompleteDevissageOver.stage k).Y.hom g (y' k) = s')

include h_point h_x_snd in
/-- The image of a lifted source point is the base point for the canonical unpointed
base change. -/
theorem liftedBasePoint_eq :
    g (pullback.snd f g x') = f x := sorry

/-- The canonical unpointed base change underlying the transported complete dévissage. -/
noncomputable def underlyingBaseChange :
    CompleteDevissageOver (pullback.snd f g) (Scheme.Modules.baseChangeModule f g F)
      (pullback.snd f g x') :=
  D.toCompleteDevissageOver.baseChangeCanonical g (pullback.snd f g x')
    (liftedBasePoint_eq g s' h_point x' h_x_snd)

include D h_point h_residue h_x_fst h_x_snd in
/-- The transported source point has maximal ambient fibre-support dimension. -/
theorem initialMaximalSupportDimension :
    ambientFiberSupportDimensionAt (pullback.snd f g)
        (Scheme.Modules.baseChangeModule f g F) x' =
      fiberSupportDimension (pullback.snd f g) (Scheme.Modules.baseChangeModule f g F)
        (pullback.snd f g x') := sorry

include h_residue h_x_fst h_z_fst h_z_snd in
/-- The lifted initial auxiliary point maps to the lifted source point. -/
theorem initial_i_z :
    (underlyingBaseChange D g s' h_point x' h_x_snd).initial.left (z' 0) = x' := sorry

include h_residue h_x_fst h_z_fst h_z_snd h_y_fst h_y_snd in
/-- The lifted initial auxiliary point maps to the lifted initial model point. -/
theorem initial_π_z :
    ((underlyingBaseChange D g s' h_point x' h_x_snd).stage 0).π.left
      (z' 0) = y' 0 := sorry

include h_residue h_x_fst h_z_fst h_z_snd h_y_fst h_y_snd in
/-- The fibre of the initial finite map over its lifted model point is the lifted
auxiliary point. -/
theorem initialDistinguishedFiber :
    ((underlyingBaseChange D g s' h_point x' h_x_snd).stage 0).π.left ⁻¹'
      {y' 0} = {z' 0} := sorry

include h_residue h_x_fst h_y_fst h_y_snd in
/-- The lifted initial model point lies over the image of the lifted source point. -/
theorem initialModelPoint :
    ((underlyingBaseChange D g s' h_point x' h_x_snd).stage 0).Y.hom
      (y' 0) = pullback.snd f g x' := sorry

include h_residue h_x_fst h_y_fst h_y_snd in
/-- The residue-field extension at the lifted initial model point is purely
transcendental. -/
theorem initialResidueExtension :
    let D' := underlyingBaseChange D g s' h_point x' h_x_snd
    let h_base : (D'.stage 0).Y.hom (y' 0) = pullback.snd f g x' :=
      initialModelPoint D g s' h_point x' h_x_fst h_x_snd y' h_y_fst h_y_snd
    ((S'.residueFieldCongr h_base).inv ≫
      (D'.stage 0).Y.hom.residueFieldMap (y' 0)).hom.IsPurelyTranscendental := sorry

/-- The ambient-point refinement of the initial canonically pulled-back stage. -/
noncomputable def initialBaseChange :
    @OneStepDevissageAtAmbientPoint S' ((Over.pullback g).obj (Over.mk f))
      (Scheme.Modules.baseChangeModule f g F)
      (@OneStepDevissage.baseChange_locallyOfFiniteType S S' (Over.mk f) g h_f)
      (@OneStepDevissage.baseChangeModule_isQuasicoherent S S' (Over.mk f) F g h_Fqc)
      (@OneStepDevissage.baseChangeModule_isFiniteType S S' (Over.mk f) F g h_Fft) x' :=
  let D' := underlyingBaseChange D g s' h_point x' h_x_snd
  @OneStepDevissageAtAmbientPoint.ofDiagram S' ((Over.pullback g).obj (Over.mk f))
    (Scheme.Modules.baseChangeModule f g F)
    (@OneStepDevissage.baseChange_locallyOfFiniteType S S' (Over.mk f) g h_f)
    (@OneStepDevissage.baseChangeModule_isQuasicoherent S S' (Over.mk f) F g h_Fqc)
    (@OneStepDevissage.baseChangeModule_isFiniteType S S' (Over.mk f) F g h_Fft) x'
    D'.initialStep.toOneStepDevissage
    (initialMaximalSupportDimension D g s' h_point x' h_x_fst h_x_snd)
    (z' 0) (y' 0)
    (initial_i_z D g s' h_point x' h_x_fst h_x_snd z' h_z_fst h_z_snd)
    (initial_π_z D g s' h_point x' h_x_fst h_x_snd z' h_z_fst h_z_snd
      y' h_y_fst h_y_snd)
    (initialDistinguishedFiber D g s' h_point x' h_x_fst h_x_snd
      z' h_z_fst h_z_snd y' h_y_fst h_y_snd)
    (initialModelPoint D g s' h_point x' h_x_fst h_x_snd y' h_y_fst h_y_snd)
    (initialResidueExtension D g s' h_point x' h_x_fst h_x_snd y' h_y_fst h_y_snd)

/-- The initial ambient-point refinement is the first stage of the canonical unpointed
base change. -/
theorem initialCompatibilityProof :
    @OneStepDevissageAtAmbientPoint.IsStage S' ((Over.pullback g).obj (Over.mk f))
      (Scheme.Modules.baseChangeModule f g F)
      (@OneStepDevissage.baseChange_locallyOfFiniteType S S' (Over.mk f) g h_f)
      (@OneStepDevissage.baseChangeModule_isQuasicoherent S S' (Over.mk f) F g h_Fqc)
      (@OneStepDevissage.baseChangeModule_isFiniteType S S' (Over.mk f) F g h_Fft) x'
      (pullback.snd f g x')
      (initialBaseChange D g s' h_point x' h_x_fst h_x_snd
        z' h_z_fst h_z_snd y' h_y_fst h_y_snd)
      ((underlyingBaseChange D g s' h_point x' h_x_snd).stage 0)
      (underlyingBaseChange D g s' h_point x' h_x_snd).initial := sorry

/-- The initial ambient-point refinement retains the supplied auxiliary point. -/
theorem initialZProof :
    HEq (@OneStepDevissageAtAmbientPoint.z S' ((Over.pullback g).obj (Over.mk f))
      (Scheme.Modules.baseChangeModule f g F)
      (@OneStepDevissage.baseChange_locallyOfFiniteType S S' (Over.mk f) g h_f)
      (@OneStepDevissage.baseChangeModule_isQuasicoherent S S' (Over.mk f) F g h_Fqc)
      (@OneStepDevissage.baseChangeModule_isFiniteType S S' (Over.mk f) F g h_Fft) x'
      (initialBaseChange D g s' h_point x' h_x_fst h_x_snd
        z' h_z_fst h_z_snd y' h_y_fst h_y_snd)) (z' 0) := sorry

/-- The initial ambient-point refinement retains the supplied model point. -/
theorem initialYProof :
    HEq (@OneStepDevissageAtAmbientPoint.y S' ((Over.pullback g).obj (Over.mk f))
      (Scheme.Modules.baseChangeModule f g F)
      (@OneStepDevissage.baseChange_locallyOfFiniteType S S' (Over.mk f) g h_f)
      (@OneStepDevissage.baseChangeModule_isQuasicoherent S S' (Over.mk f) F g h_Fqc)
      (@OneStepDevissage.baseChangeModule_isFiniteType S S' (Over.mk f) F g h_Fft) x'
      (initialBaseChange D g s' h_point x' h_x_fst h_x_snd
        z' h_z_fst h_z_snd y' h_y_fst h_y_snd)) (y' 0) := sorry

include h_residue h_y_fst h_y_snd in
/-- A lifted predecessor model point lies over the actual base point of the lifted source
point. -/
theorem successorBasePoint (i : Fin D.toCompleteDevissageOver.last) :
    ((underlyingBaseChange D g s' h_point x' h_x_snd).stage i.castSucc).Y.hom
      (y' i.castSucc) = pullback.snd f g x' := sorry

include h_residue h_y_fst h_y_snd in
/-- The fibre-dimension law for a canonical successor stage at its lifted predecessor
point. -/
theorem successorFiberDimension (i : Fin D.toCompleteDevissageOver.last) :
    ((underlyingBaseChange D g s' h_point x' h_x_snd).stage i.succ).Y.hom.fiberDimension =
      fun _ ↦ fiberSupportDimension
        ((underlyingBaseChange D g s' h_point x' h_x_snd).stage i.castSucc).Y.hom
        (cokernel
          ((underlyingBaseChange D g s' h_point x' h_x_snd).stage i.castSucc).α)
        (((underlyingBaseChange D g s' h_point x' h_x_snd).stage i.castSucc).Y.hom
          (y' i.castSucc)) := sorry

/-- The unpointed successor stage reindexed at its lifted predecessor model point. -/
noncomputable def successorUnderlying
    (i : Fin D.toCompleteDevissageOver.last) :
    let D' := underlyingBaseChange D g s' h_point x' h_x_snd
    @OneStepDevissage S' (D'.stage i.castSucc).Y
      (cokernel (D'.stage i.castSucc).α)
      (D'.transitionStep i).locallyOfFiniteType
      (D'.transitionStep i).sourceQuasicoherent
      (D'.transitionStep i).sourceFiniteType
      ((D'.stage i.castSucc).Y.hom (y' i.castSucc)) :=
  let D' := underlyingBaseChange D g s' h_point x' h_x_snd
  @OneStepDevissage.ofDiagram S' (D'.stage i.castSucc).Y
    (cokernel (D'.stage i.castSucc).α)
    (D'.transitionStep i).locallyOfFiniteType
    (D'.transitionStep i).sourceQuasicoherent
    (D'.transitionStep i).sourceFiniteType
    ((D'.stage i.castSucc).Y.hom (y' i.castSucc))
    (D'.stage i.succ).Z (D'.stage i.succ).Y (D'.transition i)
    (D'.stage i.succ).π (D'.stage i.succ).G
    (D'.transitionStep i).isAffineS (D'.transitionStep i).isAffineX
    (D'.transitionStep i).isAffineZ (D'.transitionStep i).isAffineY
    (D'.transitionStep i).isClosedImmersion (D'.transitionStep i).finitePresentation
    (D'.transitionStep i).quasicoherent (D'.transitionStep i).finiteType
    (D'.transitionStep i).moduleIso (D'.transitionStep i).finite
    (D'.transitionStep i).smooth (D'.transitionStep i).geometricallyIrreducible
    (successorFiberDimension D g s' h_point x' h_x_snd y' h_y_fst h_y_snd i)

include h_residue h_y_fst h_y_snd in
/-- The lifted predecessor point has maximal ambient fibre-support dimension for the
successor source module. -/
theorem successorMaximalSupportDimension
    (i : Fin D.toCompleteDevissageOver.last) :
    let D' := underlyingBaseChange D g s' h_point x' h_x_snd
    ambientFiberSupportDimensionAt (D'.stage i.castSucc).Y.hom
        (cokernel (D'.stage i.castSucc).α) (y' i.castSucc) =
      fiberSupportDimension (D'.stage i.castSucc).Y.hom
        (cokernel (D'.stage i.castSucc).α)
        ((D'.stage i.castSucc).Y.hom (y' i.castSucc)) := sorry

include h_residue h_z_fst h_z_snd h_y_fst h_y_snd in
/-- The lifted successor auxiliary point maps to the lifted predecessor model point. -/
theorem successor_i_z (i : Fin D.toCompleteDevissageOver.last) :
    ((underlyingBaseChange D g s' h_point x' h_x_snd).transition i).left
      (z' i.succ) = y' i.castSucc := sorry

include h_residue h_z_fst h_z_snd h_y_fst h_y_snd in
/-- The lifted successor auxiliary point maps to the lifted successor model point. -/
theorem successor_π_z (i : Fin D.toCompleteDevissageOver.last) :
    ((underlyingBaseChange D g s' h_point x' h_x_snd).stage i.succ).π.left
      (z' i.succ) = y' i.succ := sorry

include h_residue h_z_fst h_z_snd h_y_fst h_y_snd in
/-- The fibre of a successor finite map over its lifted model point is the lifted
auxiliary point. -/
theorem successorDistinguishedFiber (i : Fin D.toCompleteDevissageOver.last) :
    ((underlyingBaseChange D g s' h_point x' h_x_snd).stage i.succ).π.left ⁻¹'
      {y' i.succ} = {z' i.succ} := sorry

include h_residue h_y_fst h_y_snd in
/-- A lifted successor model point lies over the lifted predecessor model point. -/
theorem successorModelPoint (i : Fin D.toCompleteDevissageOver.last) :
    ((underlyingBaseChange D g s' h_point x' h_x_snd).stage i.succ).Y.hom
      (y' i.succ) =
        ((underlyingBaseChange D g s' h_point x' h_x_snd).stage i.castSucc).Y.hom
          (y' i.castSucc) := sorry

include h_residue h_y_fst h_y_snd in
/-- The residue-field extension at a lifted successor model point is purely
transcendental. -/
theorem successorResidueExtension (i : Fin D.toCompleteDevissageOver.last) :
    let D' := underlyingBaseChange D g s' h_point x' h_x_snd
    let h_base : (D'.stage i.succ).Y.hom (y' i.succ) =
        (D'.stage i.castSucc).Y.hom (y' i.castSucc) :=
      successorModelPoint D g s' h_point x' h_x_snd y' h_y_fst h_y_snd i
    ((S'.residueFieldCongr h_base).inv ≫
      (D'.stage i.succ).Y.hom.residueFieldMap (y' i.succ)).hom.IsPurelyTranscendental := sorry

/-- The ambient-point refinement of a canonical successor stage. -/
noncomputable def successorBaseChange
    (i : Fin D.toCompleteDevissageOver.last) :
    let D' := underlyingBaseChange D g s' h_point x' h_x_snd
    @OneStepDevissageAtAmbientPoint S' (D'.stage i.castSucc).Y
      (cokernel (D'.stage i.castSucc).α)
      (D'.transitionStep i).locallyOfFiniteType
      (D'.transitionStep i).sourceQuasicoherent
      (D'.transitionStep i).sourceFiniteType (y' i.castSucc) :=
  let D' := underlyingBaseChange D g s' h_point x' h_x_snd
  @OneStepDevissageAtAmbientPoint.ofDiagram S' (D'.stage i.castSucc).Y
    (cokernel (D'.stage i.castSucc).α)
    (D'.transitionStep i).locallyOfFiniteType
    (D'.transitionStep i).sourceQuasicoherent
    (D'.transitionStep i).sourceFiniteType (y' i.castSucc)
    (successorUnderlying D g s' h_point x' h_x_snd y' h_y_fst h_y_snd i)
    (successorMaximalSupportDimension D g s' h_point x' h_x_snd y' h_y_fst h_y_snd i)
    (z' i.succ) (y' i.succ)
    (successor_i_z D g s' h_point x' h_x_snd z' h_z_fst h_z_snd
      y' h_y_fst h_y_snd i)
    (successor_π_z D g s' h_point x' h_x_snd z' h_z_fst h_z_snd
      y' h_y_fst h_y_snd i)
    (successorDistinguishedFiber D g s' h_point x' h_x_snd
      z' h_z_fst h_z_snd y' h_y_fst h_y_snd i)
    (successorModelPoint D g s' h_point x' h_x_snd y' h_y_fst h_y_snd i)
    (successorResidueExtension D g s' h_point x' h_x_snd y' h_y_fst h_y_snd i)

/-- A successor ambient-point refinement is its corresponding canonical successor
stage. -/
theorem successorCompatibilityProof (i : Fin D.toCompleteDevissageOver.last) :
    let D' := underlyingBaseChange D g s' h_point x' h_x_snd
    @OneStepDevissageAtAmbientPoint.IsStage S' (D'.stage i.castSucc).Y
      (cokernel (D'.stage i.castSucc).α)
      (D'.transitionStep i).locallyOfFiniteType
      (D'.transitionStep i).sourceQuasicoherent
      (D'.transitionStep i).sourceFiniteType (y' i.castSucc)
      (pullback.snd f g x')
      (successorBaseChange D g s' h_point x' h_x_snd
        z' h_z_fst h_z_snd y' h_y_fst h_y_snd i)
      (D'.stage i.succ) (D'.transition i) := sorry

/-- A successor ambient-point refinement retains its supplied auxiliary point. -/
theorem successorZProof (i : Fin D.toCompleteDevissageOver.last) :
    let D' := underlyingBaseChange D g s' h_point x' h_x_snd
    HEq (@OneStepDevissageAtAmbientPoint.z S' (D'.stage i.castSucc).Y
      (cokernel (D'.stage i.castSucc).α)
      (D'.transitionStep i).locallyOfFiniteType
      (D'.transitionStep i).sourceQuasicoherent
      (D'.transitionStep i).sourceFiniteType (y' i.castSucc)
      (successorBaseChange D g s' h_point x' h_x_snd
        z' h_z_fst h_z_snd y' h_y_fst h_y_snd i)) (z' i.succ) := sorry

/-- A successor ambient-point refinement retains its supplied model point. -/
theorem successorYProof (i : Fin D.toCompleteDevissageOver.last) :
    let D' := underlyingBaseChange D g s' h_point x' h_x_snd
    HEq (@OneStepDevissageAtAmbientPoint.y S' (D'.stage i.castSucc).Y
      (cokernel (D'.stage i.castSucc).α)
      (D'.transitionStep i).locallyOfFiniteType
      (D'.transitionStep i).sourceQuasicoherent
      (D'.transitionStep i).sourceFiniteType (y' i.castSucc)
      (successorBaseChange D g s' h_point x' h_x_snd
        z' h_z_fst h_z_snd y' h_y_fst h_y_snd i)) (y' i.succ) := sorry

/-- Pull a complete dévissage at an ambient point back along an affine pointed morphism
that induces an isomorphism on residue fields. -/
noncomputable def baseChange :
    @CompleteDevissageAtAmbientPoint S' (Limits.pullback f g) (pullback.snd f g)
      (Scheme.Modules.baseChangeModule f g F)
      (@OneStepDevissage.baseChange_locallyOfFiniteType S S' (Over.mk f) g h_f)
      (@OneStepDevissage.baseChangeModule_isQuasicoherent S S' (Over.mk f) F g h_Fqc)
      (@OneStepDevissage.baseChangeModule_isFiniteType S S' (Over.mk f) F g h_Fft) x' :=
  let D' := underlyingBaseChange D g s' h_point x' h_x_snd
  CompleteDevissageAtAmbientPoint.ofStages D' z' y'
    (initialBaseChange D g s' h_point x' h_x_fst h_x_snd
      z' h_z_fst h_z_snd y' h_y_fst h_y_snd)
    (initialCompatibilityProof D g s' h_point x' h_x_fst h_x_snd
      z' h_z_fst h_z_snd y' h_y_fst h_y_snd)
    (initialZProof D g s' h_point x' h_x_fst h_x_snd
      z' h_z_fst h_z_snd y' h_y_fst h_y_snd)
    (initialYProof D g s' h_point x' h_x_fst h_x_snd
      z' h_z_fst h_z_snd y' h_y_fst h_y_snd)
    (fun i ↦ successorBaseChange D g s' h_point x' h_x_snd
      z' h_z_fst h_z_snd y' h_y_fst h_y_snd i)
    (successorCompatibilityProof D g s' h_point x' h_x_snd
      z' h_z_fst h_z_snd y' h_y_fst h_y_snd)
    (successorZProof D g s' h_point x' h_x_snd
      z' h_z_fst h_z_snd y' h_y_fst h_y_snd)
    (successorYProof D g s' h_point x' h_x_snd
      z' h_z_fst h_z_snd y' h_y_fst h_y_snd)

/-- The underlying complete dévissage is the canonical unpointed base change. -/
theorem baseChange_toCompleteDevissageOver :
    (baseChange D g s' h_point x' h_x_fst h_x_snd
      z' h_z_fst h_z_snd y' h_y_fst h_y_snd).toCompleteDevissageOver =
      D.toCompleteDevissageOver.baseChangeCanonical g (pullback.snd f g x')
        (liftedBasePoint_eq g s' h_point x' h_x_snd) := sorry

/-- Every auxiliary point of the transported complete dévissage is its supplied lift. -/
theorem baseChange_z (k : Fin (D.toCompleteDevissageOver.last + 1)) :
    HEq ((baseChange D g s' h_point x' h_x_fst h_x_snd
      z' h_z_fst h_z_snd y' h_y_fst h_y_snd).z k) (z' k) := sorry

/-- Every model point of the transported complete dévissage is its supplied lift. -/
theorem baseChange_y (k : Fin (D.toCompleteDevissageOver.last + 1)) :
    HEq ((baseChange D g s' h_point x' h_x_fst h_x_snd
      z' h_z_fst h_z_snd y' h_y_fst h_y_snd).y k) (y' k) := sorry

/-- The initial ambient-point step of the transported complete dévissage is the constructed
initial refinement. -/
theorem baseChange_initialStep :
    HEq (@CompleteDevissageAtAmbientPoint.initialStep S' (Limits.pullback f g)
      (pullback.snd f g) (Scheme.Modules.baseChangeModule f g F)
      (@OneStepDevissage.baseChange_locallyOfFiniteType S S' (Over.mk f) g h_f)
      (@OneStepDevissage.baseChangeModule_isQuasicoherent S S' (Over.mk f) F g h_Fqc)
      (@OneStepDevissage.baseChangeModule_isFiniteType S S' (Over.mk f) F g h_Fft) x'
      (baseChange D g s' h_point x' h_x_fst h_x_snd
        z' h_z_fst h_z_snd y' h_y_fst h_y_snd))
      (initialBaseChange D g s' h_point x' h_x_fst h_x_snd
        z' h_z_fst h_z_snd y' h_y_fst h_y_snd) := sorry

/-- Every successor ambient-point step of the transported complete dévissage is its
constructed successor refinement. -/
theorem baseChange_successorStep (i : Fin D.toCompleteDevissageOver.last) :
    let D' := D.toCompleteDevissageOver.baseChangeCanonical g (pullback.snd f g x')
      (liftedBasePoint_eq g s' h_point x' h_x_snd)
    HEq (@CompleteDevissageAtAmbientPoint.successorStep S' (Limits.pullback f g)
      (pullback.snd f g) (Scheme.Modules.baseChangeModule f g F)
      (@OneStepDevissage.baseChange_locallyOfFiniteType S S' (Over.mk f) g h_f)
      (@OneStepDevissage.baseChangeModule_isQuasicoherent S S' (Over.mk f) F g h_Fqc)
      (@OneStepDevissage.baseChangeModule_isFiniteType S S' (Over.mk f) F g h_Fft) x'
      (baseChange D g s' h_point x' h_x_fst h_x_snd
        z' h_z_fst h_z_snd y' h_y_fst h_y_snd) i)
      (successorBaseChange D g s' h_point x' h_x_snd
        z' h_z_fst h_z_snd y' h_y_fst h_y_snd i) := sorry

end

end AlgebraicGeometry.Scheme.Modules.CompleteDevissageAtAmbientPoint
