/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.SimplicialScheme.Zariski
public import ReasLib.Topology.Category.TopCat.DiagramOpens.SimplicialMap
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.PullbackMixedUniverse
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous

/-!
# Pullback of modules on simplicial schemes

Componentwise structure-sheaf maps induce inverse image of module sheaves on
the simplicial Zariski sites.
-/

@[expose] public section

open CategoryTheory CategoryTheory.SimplicialObject Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SimplicialObject

/-- The map on sections induced by a component of a morphism of simplicial schemes. -/
def structureSheafMapApp {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U)
    (W : (zariskiSite (forgetToTop.obj U))ᵒᵖ) :
    (structureSheaf U).obj.obj W ⟶
      (structureSheaf V).obj.obj (op ((zariskiMap (forgetToTop.map f)).obj W.unop)) :=
  (f.app W.unop.base).toRingCatSheafHom.hom.app (op W.unop.opens)

/-- The componentwise structure-sheaf maps commute with restriction along diagram opens. -/
theorem structureSheafMap_naturality {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U)
    {W Z : (zariskiSite (forgetToTop.obj U))ᵒᵖ} (η : W ⟶ Z) :
    (structureSheaf U).obj.map η ≫ structureSheafMapApp f Z =
      structureSheafMapApp f W ≫
        (structureSheaf V).obj.map ((zariskiMap (forgetToTop.map f)).op.map η) :=
  sorry

/-- The structure-sheaf morphism induced by a morphism of simplicial schemes. -/
def structureSheafMap {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U) :
    structureSheaf U ⟶
      ((zariskiMap (forgetToTop.map f)).sheafPushforwardContinuous RingCat.{u}
        (zariskiTopology (forgetToTop.obj U)) (zariskiTopology (forgetToTop.obj V))).obj
        (structureSheaf V) :=
  ⟨{ app := structureSheafMapApp f
     naturality := fun _ _ η ↦ structureSheafMap_naturality f η }⟩

/-- The structure-sheaf morphism acts by the componentwise scheme maps on sections. -/
theorem structureSheafMap_app {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U)
    (W : (zariskiSite (forgetToTop.obj U))ᵒᵖ) :
    (structureSheafMap f).hom.app W = structureSheafMapApp f W := rfl

/-- Inverse image of module sheaves along a morphism of simplicial schemes. -/
def modulePullback {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U) :
    SheafOfModules.{u} (structureSheaf U) ⥤ SheafOfModules.{u} (structureSheaf V) :=
  SheafOfModules.pullback (structureSheafMap f)

end AlgebraicGeometry.SimplicialObject
