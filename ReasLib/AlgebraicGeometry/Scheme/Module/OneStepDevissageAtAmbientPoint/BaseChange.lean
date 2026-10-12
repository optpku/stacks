/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.OneStepDevissageAtAmbientPoint
public import ReasLib.AlgebraicGeometry.Scheme.Module.OneStepDevissage.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Pullback.ResidueField

/-!
# Base change of one-step dévissages at ambient fibre points

This module transports the distinguished points and fibre conditions of an
ambient-point one-step dévissage across a pointed affine base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S S' : Scheme.{u}} {X : Over S} {F : X.left.Modules}
  [h_locallyOfFiniteType : LocallyOfFiniteType X.hom]
  [h_quasicoherent : F.IsQuasicoherent] [h_finiteType : F.IsFiniteType] {x : X.left}

section

variable (D : OneStepDevissageAtAmbientPoint X F x) (g : S' ⟶ S) (s' : S')
  (h_point : g s' = X.hom x) [h_affine : IsAffine S']
  [h_residue : IsIso (g.residueFieldMap s')]
  (x' : (CategoryTheory.Limits.pullback X.hom g : Scheme))
  (h_x_fst : pullback.fst X.hom g x' = x)
  (h_x_snd : pullback.snd X.hom g x' = s')
  (z' : (CategoryTheory.Limits.pullback D.toOneStepDevissage.Z.hom g : Scheme))
  (h_z_fst : pullback.fst D.toOneStepDevissage.Z.hom g z' = D.z)
  (h_z_snd : pullback.snd D.toOneStepDevissage.Z.hom g z' = s')
  (y' : (CategoryTheory.Limits.pullback D.toOneStepDevissage.Y.hom g : Scheme))
  (h_y_fst : pullback.fst D.toOneStepDevissage.Y.hom g y' = D.y)
  (h_y_snd : pullback.snd D.toOneStepDevissage.Y.hom g y' = s')

include h_point h_x_snd in
/-- The pullback source point lies over the image of the original distinguished point. -/
theorem transportedPoint_eq :
    g (pullback.snd X.hom g x') = X.hom x := sorry

include D h_point h_residue h_x_fst h_x_snd in
/-- The ambient fibre-support dimension remains maximal at the transported point. -/
theorem transportedMaximalSupportDimension :
    ambientFiberSupportDimensionAt (pullback.snd X.hom g)
        (Scheme.Modules.baseChangeModule X.hom g F) x' =
      fiberSupportDimension (pullback.snd X.hom g)
        (Scheme.Modules.baseChangeModule X.hom g F) (pullback.snd X.hom g x') := sorry

include h_point h_residue h_x_fst h_x_snd h_z_fst h_z_snd in
/-- The transported auxiliary point maps to the distinguished source point. -/
theorem transported_i_z :
    ((Over.pullback g).map D.toOneStepDevissage.i).left z' = x' := sorry

include h_point h_residue h_x_fst h_x_snd h_z_fst h_z_snd h_y_fst h_y_snd in
/-- The transported auxiliary point maps to the transported model point. -/
theorem transported_π_z :
    ((Over.pullback g).map D.toOneStepDevissage.π).left z' = y' := sorry

include h_point h_residue h_x_fst h_x_snd h_z_fst h_z_snd h_y_fst h_y_snd in
/-- The fibre over the transported model point consists of the transported auxiliary point. -/
theorem transportedDistinguishedFiber :
    ((Over.pullback g).map D.toOneStepDevissage.π).left ⁻¹' {y'} = {z'} := sorry

include h_point h_residue h_x_fst h_x_snd h_y_fst h_y_snd in
/-- The transported model point lies over the transported base point. -/
theorem transportedModelPoint :
    ((Over.pullback g).obj D.toOneStepDevissage.Y).hom y' =
      pullback.snd X.hom g x' := sorry

include h_point h_residue h_x_fst h_x_snd h_y_fst h_y_snd in
/-- The transported residue-field extension is purely transcendental. -/
theorem transportedResidueExtension :
    let Y' := (Over.pullback g).obj D.toOneStepDevissage.Y
    let h_base : Y'.hom y' = pullback.snd X.hom g x' :=
      transportedModelPoint D g s' h_point x' h_x_fst h_x_snd y' h_y_fst h_y_snd
    ((S'.residueFieldCongr h_base).inv ≫
      Y'.hom.residueFieldMap y').hom.IsPurelyTranscendental := sorry

include D h_locallyOfFiniteType h_quasicoherent h_finiteType in
/-- Pull an ambient-point one-step dévissage back along a pointed morphism whose source
is affine and whose residue-field map at the distinguished point is an isomorphism. -/
noncomputable def baseChange :
    @OneStepDevissageAtAmbientPoint S' ((Over.pullback g).obj X)
      (Scheme.Modules.baseChangeModule X.hom g F :
        ((Over.pullback g).obj X).left.Modules)
      (@OneStepDevissage.baseChange_locallyOfFiniteType S S' X g h_locallyOfFiniteType)
      (@OneStepDevissage.baseChangeModule_isQuasicoherent S S' X F g h_quasicoherent)
      (@OneStepDevissage.baseChangeModule_isFiniteType S S' X F g h_finiteType) x' :=
  let h_basePoint := transportedPoint_eq g s' h_point x' h_x_snd
  let E := D.toOneStepDevissage.baseChange g (pullback.snd X.hom g x') h_basePoint
  @OneStepDevissageAtAmbientPoint.ofDiagram S' ((Over.pullback g).obj X)
    (Scheme.Modules.baseChangeModule X.hom g F :
      ((Over.pullback g).obj X).left.Modules)
    (@OneStepDevissage.baseChange_locallyOfFiniteType S S' X g h_locallyOfFiniteType)
    (@OneStepDevissage.baseChangeModule_isQuasicoherent S S' X F g h_quasicoherent)
    (@OneStepDevissage.baseChangeModule_isFiniteType S S' X F g h_finiteType)
    x' E
    (transportedMaximalSupportDimension D g s' h_point x' h_x_fst h_x_snd)
    z' y'
    (transported_i_z D g s' h_point x' h_x_fst h_x_snd z' h_z_fst h_z_snd)
    (transported_π_z D g s' h_point x' h_x_fst h_x_snd z' h_z_fst h_z_snd
      y' h_y_fst h_y_snd)
    (transportedDistinguishedFiber D g s' h_point x' h_x_fst h_x_snd z'
      h_z_fst h_z_snd y' h_y_fst h_y_snd)
    (transportedModelPoint D g s' h_point x' h_x_fst h_x_snd y' h_y_fst h_y_snd)
    (transportedResidueExtension D g s' h_point x' h_x_fst h_x_snd
      y' h_y_fst h_y_snd)

include h_locallyOfFiniteType h_quasicoherent h_finiteType in
/-- The underlying dévissage of the ambient-point base change is the canonical unpointed
base change at the induced base point. -/
theorem baseChange_toOneStepDevissage :
    @OneStepDevissageAtAmbientPoint.toOneStepDevissage S' ((Over.pullback g).obj X)
        (Scheme.Modules.baseChangeModule X.hom g F)
        (@OneStepDevissage.baseChange_locallyOfFiniteType S S' X g h_locallyOfFiniteType)
        (@OneStepDevissage.baseChangeModule_isQuasicoherent S S' X F g h_quasicoherent)
        (@OneStepDevissage.baseChangeModule_isFiniteType S S' X F g h_finiteType) x'
        (baseChange D g s' h_point x' h_x_fst h_x_snd z' h_z_fst h_z_snd
          y' h_y_fst h_y_snd) =
      D.toOneStepDevissage.baseChange g (pullback.snd X.hom g x')
        (transportedPoint_eq g s' h_point x' h_x_snd) := sorry

include h_locallyOfFiniteType h_quasicoherent h_finiteType in
/-- The auxiliary distinguished point of the ambient-point base change is the supplied
pullback point. -/
theorem baseChange_z :
    @OneStepDevissageAtAmbientPoint.z S' ((Over.pullback g).obj X)
        (Scheme.Modules.baseChangeModule X.hom g F)
        (@OneStepDevissage.baseChange_locallyOfFiniteType S S' X g h_locallyOfFiniteType)
        (@OneStepDevissage.baseChangeModule_isQuasicoherent S S' X F g h_quasicoherent)
        (@OneStepDevissage.baseChangeModule_isFiniteType S S' X F g h_finiteType) x'
        (baseChange D g s' h_point x' h_x_fst h_x_snd z' h_z_fst h_z_snd
          y' h_y_fst h_y_snd) = z' := sorry

include h_locallyOfFiniteType h_quasicoherent h_finiteType in
/-- The model distinguished point of the ambient-point base change is the supplied
pullback point. -/
theorem baseChange_y :
    @OneStepDevissageAtAmbientPoint.y S' ((Over.pullback g).obj X)
        (Scheme.Modules.baseChangeModule X.hom g F)
        (@OneStepDevissage.baseChange_locallyOfFiniteType S S' X g h_locallyOfFiniteType)
        (@OneStepDevissage.baseChangeModule_isQuasicoherent S S' X F g h_quasicoherent)
        (@OneStepDevissage.baseChangeModule_isFiniteType S S' X F g h_finiteType) x'
        (baseChange D g s' h_point x' h_x_fst h_x_snd z' h_z_fst h_z_snd
          y' h_y_fst h_y_snd) = y' := sorry

include h_locallyOfFiniteType h_quasicoherent h_finiteType in
/-- The ambient-point base change has the canonical underlying dévissage and retains the
supplied auxiliary and model points. -/
theorem baseChange_spec :
    @OneStepDevissageAtAmbientPoint.toOneStepDevissage S' ((Over.pullback g).obj X)
        (Scheme.Modules.baseChangeModule X.hom g F)
        (@OneStepDevissage.baseChange_locallyOfFiniteType S S' X g h_locallyOfFiniteType)
        (@OneStepDevissage.baseChangeModule_isQuasicoherent S S' X F g h_quasicoherent)
        (@OneStepDevissage.baseChangeModule_isFiniteType S S' X F g h_finiteType) x'
        (baseChange D g s' h_point x' h_x_fst h_x_snd z' h_z_fst h_z_snd
          y' h_y_fst h_y_snd) =
        D.toOneStepDevissage.baseChange g (pullback.snd X.hom g x')
          (transportedPoint_eq g s' h_point x' h_x_snd) ∧
      @OneStepDevissageAtAmbientPoint.z S' ((Over.pullback g).obj X)
          (Scheme.Modules.baseChangeModule X.hom g F)
          (@OneStepDevissage.baseChange_locallyOfFiniteType S S' X g h_locallyOfFiniteType)
          (@OneStepDevissage.baseChangeModule_isQuasicoherent S S' X F g h_quasicoherent)
          (@OneStepDevissage.baseChangeModule_isFiniteType S S' X F g h_finiteType) x'
          (baseChange D g s' h_point x' h_x_fst h_x_snd z' h_z_fst h_z_snd
            y' h_y_fst h_y_snd) = z' ∧
      @OneStepDevissageAtAmbientPoint.y S' ((Over.pullback g).obj X)
          (Scheme.Modules.baseChangeModule X.hom g F)
          (@OneStepDevissage.baseChange_locallyOfFiniteType S S' X g h_locallyOfFiniteType)
          (@OneStepDevissage.baseChangeModule_isQuasicoherent S S' X F g h_quasicoherent)
          (@OneStepDevissage.baseChangeModule_isFiniteType S S' X F g h_finiteType) x'
          (baseChange D g s' h_point x' h_x_fst h_x_snd z' h_z_fst h_z_snd
            y' h_y_fst h_y_snd) = y' := sorry

end

end AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint
