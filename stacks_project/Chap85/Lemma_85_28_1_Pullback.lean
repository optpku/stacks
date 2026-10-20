/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback
public import ReasLib.AlgebraicGeometry.SimplicialScheme.Module.Pullback
public import stacks_project.Chap85.Lemma_85_2_3
public import stacks_project.Chap85.Lemma_85_28_1_Ringed

/-!
# Ringed morphisms of Zariski sites of simplicial schemes

A morphism of simplicial schemes induces a morphism of Zariski ringed sites, with
underlying site functor `zariskiMap` and structure-sheaf map assembled from the
stagewise maps `toRingCatSheafHom`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.SimplicialObject Opposite AlgebraicGeometry
open RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.SimplicialObject

/-- The morphism of Zariski ringed sites associated to a morphism of simplicial schemes. -/
def zariskiRingedHom {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U) :
    Hom (zariskiRingedSite V) (zariskiRingedSite U) where
  base := zariskiMap (forgetToTop.map f)
  structureSheafMap := structureSheafMap f

/-- The underlying site functor of `zariskiRingedHom f` is `zariskiMap` of the underlying
morphism of simplicial spaces. -/
theorem zariskiRingedHom_base {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U) :
    (zariskiRingedHom f).base = zariskiMap (forgetToTop.map f) :=
  rfl

/-- Module pushforward along `zariskiRingedHom f` is a right adjoint, so module pullback exists. -/
theorem zariskiRingedHom.modulePushforward_isRightAdjoint
    {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U) :
    ((zariskiRingedHom f).modulePushforward.{u}).IsRightAdjoint :=
  (SheafOfModules.PullbackConstruction.adjunction.{u} (structureSheafMap f)).isRightAdjoint

/-- `modulePullback f` is module pullback along `zariskiRingedHom f`. -/
theorem modulePullback_eq {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U) :
    modulePullback f = (zariskiRingedHom f).modulePullback.{u} :=
  rfl

end AlgebraicGeometry.SimplicialObject
