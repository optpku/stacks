/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.BaseChange.IsomorphismFunctor.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Module.ClosedImmersion.Exact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedImmersion.Quasicoherent

/-!
# Weil restrictions of closed immersions

This module realizes the Weil restriction associated to a closed immersion as an isomorphism
functor of scheme modules and records its representability by a closed immersion.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.WeilRestriction

/-- The Weil restriction attached to a closed immersion, realized as the isomorphism
functor of the structure sheaf's restriction map. -/
noncomputable def ofClosedImmersion {S : Scheme.{u}} (X Y : Over S) (i : Y ⟶ X)
    [IsClosedImmersion i.left] : (Over S)ᵒᵖ ⥤ Type u :=
  @Scheme.Modules.isomorphismFunctor S X.left X.hom
    (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules)
    ((Scheme.Modules.pushforward i.left).obj
      (SheafOfModules.unit Y.left.ringCatSheaf : Y.left.Modules))
    inferInstance
    (AlgebraicGeometry.RingedSpace.IsClosedImmersion.pushforwardUnit_isQuasicoherent
      i.left.toShHom)
    (Scheme.Modules.ClosedImmersion.restrictionMap i.left
        (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) ≫
      (Scheme.Modules.pushforward i.left).map
        (SheafOfModules.pullbackObjUnitToUnit
          (RingedSpace.Hom.toRingCatSheafHom i.left.toShHom)) :
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) ⟶
        (Scheme.Modules.pushforward i.left).obj
          (SheafOfModules.unit Y.left.ringCatSheaf : Y.left.Modules))

/-- The closed-immersion Weil restriction is inhabited at `T` exactly when the
base-changed closed immersion is an isomorphism. -/
theorem obj_nonempty_iff {S : Scheme.{u}} (X Y : Over S) (i : Y ⟶ X)
    [IsClosedImmersion i.left] (T : Over S) :
    Nonempty ((ofClosedImmersion X Y i).obj (op T)) ↔
      IsIso (((Over.pullback T.hom).map i).left) := sorry

/-- The closed-immersion Weil restriction is empty at `T` exactly when the
base-changed closed immersion is not an isomorphism. -/
theorem obj_isEmpty_iff {S : Scheme.{u}} (X Y : Over S) (i : Y ⟶ X)
    [IsClosedImmersion i.left] (T : Over S) :
    IsEmpty ((ofClosedImmersion X Y i).obj (op T)) ↔
      ¬ IsIso (((Over.pullback T.hom).map i).left) := sorry

/-- For a finitely presented, flat, pure morphism `X ⟶ S`, the Weil restriction of a
closed immersion `Y ⟶ X` is represented by a closed immersion into `S`. -/
theorem exists_closedImmersion_representation {S : Scheme.{u}} (X Y : Over S)
    (i : Y ⟶ X) [Scheme.Hom.FinitePresentation X.hom] [Flat X.hom]
    [IsClosedImmersion i.left] (h_pure : Scheme.IsPureOver X.hom) :
    ∃ Z : Over S, Nonempty ((ofClosedImmersion X Y i).RepresentableBy Z) ∧
      IsClosedImmersion Z.hom := sorry

/-- If `Y ⟶ S` is finitely presented, the closed immersion representing its Weil
restriction can be chosen finitely presented. -/
theorem exists_closedImmersion_representation_of_finitePresentation
    {S : Scheme.{u}} (X Y : Over S) (i : Y ⟶ X)
    [Scheme.Hom.FinitePresentation X.hom] [Flat X.hom]
    [IsClosedImmersion i.left] (h_pure : Scheme.IsPureOver X.hom)
    [Scheme.Hom.FinitePresentation Y.hom] :
    ∃ Z : Over S, Nonempty ((ofClosedImmersion X Y i).RepresentableBy Z) ∧
      IsClosedImmersion Z.hom ∧ Scheme.Hom.FinitePresentation Z.hom := sorry

end AlgebraicGeometry.Scheme.WeilRestriction
