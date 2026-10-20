/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Flattening
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Stratification

/-!
# Flattening stratifications

A flattening stratification represents the base-change flatness functor by a scheme whose
structural morphism is associated to a stratification. The corresponding scheme property is
the specialization to the structure module.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Flattening

/-- A quasicoherent module has a flattening stratification when its flattening functor is
represented by an object whose structural morphism is associated to a scheme stratification. -/
class HasStratification {X S : Scheme.{u}} (f : X ⟶ S)
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] : Prop where
  /-- A representing object whose structural morphism comes from a scheme stratification. -/
  exists_representation :
    ∃ S' : Over S,
      Nonempty ((functor f ℱ).RepresentableBy S') ∧ S'.hom.IsStratification

/-- A flattening stratification supplies a representation of the flattening functor. -/
instance HasStratification.isRepresentable {X S : Scheme.{u}} (f : X ⟶ S)
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [HasStratification f ℱ] :
    (functor f ℱ).IsRepresentable := sorry

/-- A quasicoherent module has a flattening stratification exactly when its flattening functor
has a representing object whose structural morphism is associated to a scheme stratification. -/
theorem hasStratification_iff {X S : Scheme.{u}} (f : X ⟶ S)
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    HasStratification f ℱ ↔
      ∃ S' : Over S,
        Nonempty ((functor f ℱ).RepresentableBy S') ∧ S'.hom.IsStratification := sorry

end AlgebraicGeometry.Scheme.Modules.Flattening

namespace AlgebraicGeometry.Scheme.Flattening

/-- A morphism of schemes has a flattening stratification when its structure module has one. -/
class HasStratification {X S : Scheme.{u}} (f : X ⟶ S) : Prop where
  /-- The flattening stratification of the structure module. -/
  structureModule :
    @Modules.Flattening.HasStratification X S f
      (AssociatedModule.structureModule X).obj
      (AssociatedModule.structureModule X).property

/-- The structure module inherits its flattening stratification from the scheme. -/
instance instModuleHasStratification {X S : Scheme.{u}} (f : X ⟶ S)
    [h : HasStratification f] :
    @Modules.Flattening.HasStratification X S f
      (AssociatedModule.structureModule X).obj
      (AssociatedModule.structureModule X).property :=
  h.structureModule

/-- A scheme morphism has a flattening stratification exactly when its structure module does. -/
theorem hasStratification_iff {X S : Scheme.{u}} (f : X ⟶ S) :
    HasStratification f ↔
      @Modules.Flattening.HasStratification X S f
        (AssociatedModule.structureModule X).obj
        (AssociatedModule.structureModule X).property := sorry

end AlgebraicGeometry.Scheme.Flattening
