/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback
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

/-- The component at a diagram open of the adjoint structure-sheaf map of a morphism of
simplicial schemes. -/
def zariskiRingedHom_structureSheafMap_app {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U)
    (W : (zariskiSite (forgetToTop.obj U))ᵒᵖ) :
    (structureSheaf U).obj.obj W ⟶
      (structureSheaf V).obj.obj (op ((zariskiMap (forgetToTop.map f)).obj W.unop)) :=
  (f.app W.unop.base).toRingCatSheafHom.hom.app (op W.unop.opens)

/-- The adjoint structure-sheaf map `𝒪_U ⟶ f_* 𝒪_V` of a morphism of simplicial schemes. -/
def zariskiRingedHom_structureSheafMap {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U) :
    structureSheaf U ⟶
      ((zariskiMap (forgetToTop.map f)).sheafPushforwardContinuous RingCat.{u}
        (zariskiTopology (forgetToTop.obj U)) (zariskiTopology (forgetToTop.obj V))).obj
        (structureSheaf V) :=
  ⟨{ app := fun W ↦ zariskiRingedHom_structureSheafMap_app f W
     naturality := fun _ _ _ ↦ sorry }⟩

/-- The morphism of Zariski ringed sites associated to a morphism of simplicial schemes. -/
def zariskiRingedHom {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U) :
    Hom (zariskiRingedSite V) (zariskiRingedSite U) where
  base := zariskiMap (forgetToTop.map f)
  structureSheafMap := zariskiRingedHom_structureSheafMap f

/-- The underlying site functor of `zariskiRingedHom f` is `zariskiMap` of the underlying
morphism of simplicial spaces. -/
theorem zariskiRingedHom_base {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U) :
    (zariskiRingedHom f).base = zariskiMap (forgetToTop.map f) :=
  rfl

/-- Module pushforward along `zariskiRingedHom f` is a right adjoint, so module pullback exists. -/
instance zariskiRingedHom.modulePushforward_isRightAdjoint
    {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U) :
    ((zariskiRingedHom f).modulePushforward.{u}).IsRightAdjoint :=
  sorry

/-- Pullback of modules along a morphism of simplicial schemes, as module inverse image on the
Zariski ringed sites. -/
abbrev modulePullback {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U) :=
  (zariskiRingedHom f).modulePullback.{u}

/-- `modulePullback f` is module pullback along `zariskiRingedHom f`. -/
theorem modulePullback_eq {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U) :
    modulePullback f = (zariskiRingedHom f).modulePullback.{u} :=
  rfl

end AlgebraicGeometry.SimplicialObject
