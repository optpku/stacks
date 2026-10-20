/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.OneStepDevissage
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.LocalGeneration
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.AffineBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.Operations

/-!
# Base change of a one-step dévissage

This module constructs the canonical pullback of a one-step dévissage along a
pointed morphism with affine source.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.OneStepDevissage

variable {S S' : Scheme.{u}} {X : Over S} {F : X.left.Modules} {s : S}

/-- The structure morphism of an `Over`-pullback is locally of finite type. -/
theorem baseChange_locallyOfFiniteType {g : S' ⟶ S} [LocallyOfFiniteType X.hom] :
    LocallyOfFiniteType ((Over.pullback g).obj X).hom := sorry

/-- Base change preserves quasicoherence of the original module. -/
theorem baseChangeModule_isQuasicoherent {g : S' ⟶ S} [F.IsQuasicoherent] :
    (Scheme.Modules.baseChangeModule X.hom g F :
      ((Over.pullback g).obj X).left.Modules).IsQuasicoherent := sorry

/-- Base change preserves finite type of the original module. -/
theorem baseChangeModule_isFiniteType {g : S' ⟶ S} [F.IsFiniteType] :
    (Scheme.Modules.baseChangeModule X.hom g F :
      ((Over.pullback g).obj X).left.Modules).IsFiniteType := sorry

section

variable [hX : LocallyOfFiniteType X.hom] [hFqc : F.IsQuasicoherent]
  [hFft : F.IsFiniteType]

/-- The pullback of the affine source of a one-step dévissage is affine. -/
theorem baseChange_affineSource (D : OneStepDevissage X F s)
    (g : S' ⟶ S) [IsAffine S'] : IsAffine ((Over.pullback g).obj X).left := sorry

/-- The pullback of the affine auxiliary scheme is affine. -/
theorem baseChange_affineAuxiliary (D : OneStepDevissage X F s)
    (g : S' ⟶ S) [IsAffine S'] : IsAffine ((Over.pullback g).obj D.Z).left := sorry

/-- The pullback of the affine smooth model is affine. -/
theorem baseChange_affineModel (D : OneStepDevissage X F s)
    (g : S' ⟶ S) [IsAffine S'] : IsAffine ((Over.pullback g).obj D.Y).left := sorry

/-- The base change of the immersion in a one-step dévissage is a closed immersion. -/
theorem baseChange_closedImmersion (D : OneStepDevissage X F s)
    (g : S' ⟶ S) : IsClosedImmersion ((Over.pullback g).map D.i).left := sorry

/-- The base change of the immersion in a one-step dévissage is of finite presentation. -/
theorem baseChange_finitePresentation (D : OneStepDevissage X F s)
    (g : S' ⟶ S) :
    Scheme.Hom.FinitePresentation ((Over.pullback g).map D.i).left := sorry

/-- The base-changed auxiliary module is quasicoherent. -/
theorem baseChange_quasicoherent (D : OneStepDevissage X F s)
    (g : S' ⟶ S) :
    (Scheme.Modules.baseChangeModule D.Z.hom g D.G).IsQuasicoherent := sorry

/-- The base-changed auxiliary module is of finite type. -/
theorem baseChange_finiteType (D : OneStepDevissage X F s)
    (g : S' ⟶ S) :
    (Scheme.Modules.baseChangeModule D.Z.hom g D.G).IsFiniteType := sorry

/-- Affine base change transports the module isomorphism in a one-step dévissage. -/
theorem baseChange_moduleIso (D : OneStepDevissage X F s) (g : S' ⟶ S)
    [IsAffine S'] :
    Nonempty
      (Scheme.Modules.baseChangeModule X.hom g F ≅
        (Scheme.Modules.pushforward ((Over.pullback g).map D.i).left).obj
          (Scheme.Modules.baseChangeModule D.Z.hom g D.G)) := sorry

/-- The base change of the finite model map is finite. -/
theorem baseChange_finite (D : OneStepDevissage X F s) (g : S' ⟶ S) :
    IsFinite ((Over.pullback g).map D.π).left := sorry

/-- The base change of the smooth model remains smooth over the new base. -/
theorem baseChange_smooth (D : OneStepDevissage X F s) (g : S' ⟶ S) :
    Smooth ((Over.pullback g).obj D.Y).hom := sorry

/-- The base change of the model has geometrically irreducible fibres. -/
theorem baseChange_geometricallyIrreducible
    (D : OneStepDevissage X F s) (g : S' ⟶ S) :
    GeometricallyIrreducible ((Over.pullback g).obj D.Y).hom := sorry

/-- Fibre dimension and support dimension agree after the pointed base change. -/
theorem baseChange_fiberDimension (D : OneStepDevissage X F s) (g : S' ⟶ S)
    (s' : S') (h_point : g s' = s) [IsAffine S'] :
    ((Over.pullback g).obj D.Y).hom.fiberDimension =
      fun _ ↦ fiberSupportDimension ((Over.pullback g).obj X).hom
        (Scheme.Modules.baseChangeModule X.hom g F) s' := sorry

/-- Pull a one-step dévissage back along a pointed morphism whose source is affine. -/
noncomputable def baseChange (D : OneStepDevissage X F s) (g : S' ⟶ S)
    (s' : S') (h_point : g s' = s) [hS' : IsAffine S'] :
    @OneStepDevissage S' ((Over.pullback g).obj X)
      (Scheme.Modules.baseChangeModule X.hom g F :
        ((Over.pullback g).obj X).left.Modules)
      (@baseChange_locallyOfFiniteType S S' X g hX)
      (@baseChangeModule_isQuasicoherent S S' X F g hFqc)
      (@baseChangeModule_isFiniteType S S' X F g hFft) s' :=
  @OneStepDevissage.ofDiagram S' ((Over.pullback g).obj X)
    (Scheme.Modules.baseChangeModule X.hom g F :
      ((Over.pullback g).obj X).left.Modules)
    (@baseChange_locallyOfFiniteType S S' X g hX)
    (@baseChangeModule_isQuasicoherent S S' X F g hFqc)
    (@baseChangeModule_isFiniteType S S' X F g hFft) s'
    ((Over.pullback g).obj D.Z) ((Over.pullback g).obj D.Y)
    ((Over.pullback g).map D.i) ((Over.pullback g).map D.π)
    (Scheme.Modules.baseChangeModule D.Z.hom g D.G)
    hS' (baseChange_affineSource D g)
    (baseChange_affineAuxiliary D g) (baseChange_affineModel D g)
    (baseChange_closedImmersion D g) (baseChange_finitePresentation D g)
    (baseChange_quasicoherent D g) (baseChange_finiteType D g)
    (baseChange_moduleIso D g) (baseChange_finite D g) (baseChange_smooth D g)
    (baseChange_geometricallyIrreducible D g)
    (baseChange_fiberDimension D g s' h_point)

/-- The auxiliary scheme of `D.baseChange g s' h_point` is the canonical pullback of `D.Z`. -/
theorem baseChange_Z (D : OneStepDevissage X F s) (g : S' ⟶ S)
    (s' : S') (h_point : g s' = s) [hS' : IsAffine S'] :
    @OneStepDevissage.Z S' ((Over.pullback g).obj X)
      (Scheme.Modules.baseChangeModule X.hom g F)
      (@baseChange_locallyOfFiniteType S S' X g hX)
      (@baseChangeModule_isQuasicoherent S S' X F g hFqc)
      (@baseChangeModule_isFiniteType S S' X F g hFft) s'
      (@baseChange S S' X F s hX hFqc hFft D g s' h_point hS') =
        (Over.pullback g).obj D.Z := sorry

/-- The model of `D.baseChange g s' h_point` is the canonical pullback of `D.Y`. -/
theorem baseChange_Y (D : OneStepDevissage X F s) (g : S' ⟶ S)
    (s' : S') (h_point : g s' = s) [hS' : IsAffine S'] :
    @OneStepDevissage.Y S' ((Over.pullback g).obj X)
      (Scheme.Modules.baseChangeModule X.hom g F)
      (@baseChange_locallyOfFiniteType S S' X g hX)
      (@baseChangeModule_isQuasicoherent S S' X F g hFqc)
      (@baseChangeModule_isFiniteType S S' X F g hFft) s'
      (@baseChange S S' X F s hX hFqc hFft D g s' h_point hS') =
        (Over.pullback g).obj D.Y := sorry

/-- The immersion of `D.baseChange g s' h_point` is the canonical pulled-back immersion. -/
theorem baseChange_i (D : OneStepDevissage X F s) (g : S' ⟶ S)
    (s' : S') (h_point : g s' = s) [hS' : IsAffine S'] :
    @OneStepDevissage.i S' ((Over.pullback g).obj X)
      (Scheme.Modules.baseChangeModule X.hom g F)
      (@baseChange_locallyOfFiniteType S S' X g hX)
      (@baseChangeModule_isQuasicoherent S S' X F g hFqc)
      (@baseChangeModule_isFiniteType S S' X F g hFft) s'
      (@baseChange S S' X F s hX hFqc hFft D g s' h_point hS') =
        (Over.pullback g).map D.i := sorry

/-- The finite map of `D.baseChange g s' h_point` is the canonical pulled-back map. -/
theorem baseChange_π (D : OneStepDevissage X F s) (g : S' ⟶ S)
    (s' : S') (h_point : g s' = s) [hS' : IsAffine S'] :
    @OneStepDevissage.π S' ((Over.pullback g).obj X)
      (Scheme.Modules.baseChangeModule X.hom g F)
      (@baseChange_locallyOfFiniteType S S' X g hX)
      (@baseChangeModule_isQuasicoherent S S' X F g hFqc)
      (@baseChangeModule_isFiniteType S S' X F g hFft) s'
      (@baseChange S S' X F s hX hFqc hFft D g s' h_point hS') =
        (Over.pullback g).map D.π := sorry

/-- The module of `D.baseChange g s' h_point` is the canonical module base change of `D.G`. -/
theorem baseChange_G (D : OneStepDevissage X F s) (g : S' ⟶ S)
    (s' : S') (h_point : g s' = s) [hS' : IsAffine S'] :
    @OneStepDevissage.G S' ((Over.pullback g).obj X)
      (Scheme.Modules.baseChangeModule X.hom g F)
      (@baseChange_locallyOfFiniteType S S' X g hX)
      (@baseChangeModule_isQuasicoherent S S' X F g hFqc)
      (@baseChangeModule_isFiniteType S S' X F g hFft) s'
      (@baseChange S S' X F s hX hFqc hFft D g s' h_point hS') =
        Scheme.Modules.baseChangeModule D.Z.hom g D.G := sorry

/-- The square defining the pulled-back immersion is cartesian. -/
theorem baseChange_i_isPullback (D : OneStepDevissage X F s) (g : S' ⟶ S) :
    IsPullback (pullback.fst D.Z.hom g) ((Over.pullback g).map D.i).left
      D.i.left (pullback.fst X.hom g) := sorry

/-- The square defining the pulled-back finite map is cartesian. -/
theorem baseChange_π_isPullback (D : OneStepDevissage X F s) (g : S' ⟶ S) :
    IsPullback (pullback.fst D.Z.hom g) ((Over.pullback g).map D.π).left
      D.π.left (pullback.fst D.Y.hom g) := sorry

end

end AlgebraicGeometry.Scheme.Modules.OneStepDevissage
