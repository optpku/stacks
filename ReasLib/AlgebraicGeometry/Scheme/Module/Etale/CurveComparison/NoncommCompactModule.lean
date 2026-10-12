/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.OppositeFiniteCharacterSheaf
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

@[expose] public section
open CategoryTheory
noncomputable section
universe u

/-- Compact Hausdorff LEFT modules over an arbitrary ring. -/
structure NoncommCompactModule (R : Type u) [Ring R] where
  toModule : ModuleCat.{u} R
  [topology : TopologicalSpace toModule]
  [compact : CompactSpace toModule]
  [t2 : T2Space toModule]
  [topologicalAdd : IsTopologicalAddGroup toModule]
  [scalarContinuous : ContinuousConstSMul R toModule]

attribute [instance] NoncommCompactModule.topology NoncommCompactModule.compact
  NoncommCompactModule.t2 NoncommCompactModule.topologicalAdd NoncommCompactModule.scalarContinuous

namespace NoncommCompactModule
variable (R : Type u) [Ring R]

instance : Category (NoncommCompactModule R) where
  Hom M N := M.toModule →L[R] N.toModule
  id M := ContinuousLinearMap.id R M.toModule
  comp f g := g.comp f
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

instance : Preadditive (NoncommCompactModule R) where
  homGroup M N := inferInstanceAs (AddCommGroup (M.toModule →L[R] N.toModule))
  add_comp P Q S f f' g := by
    apply ContinuousLinearMap.ext
    intro x
    exact (show Q.toModule →L[R] S.toModule from g).map_add _ _
  comp_add := by intros; rfl

/-- Forget topology without changing ring or handedness. -/
def forget : NoncommCompactModule R ⥤ ModuleCat.{u} R where
  obj M := M.toModule
  map f := ModuleCat.ofHom (show _ →L[R] _ from f).toLinearMap
  map_id _ := rfl
  map_comp _ _ := rfl

instance forget_additive : (forget R).Additive where
  map_add := by intros; rfl

end NoncommCompactModule

namespace NoncommCompactRepresentation
variable (R G : Type u) [Ring R] [Group G] [TopologicalSpace G]

/-- Continuity of the actual group action, with no global open-kernel condition. -/
def continuousAction : ObjectProperty (Action (NoncommCompactModule R) G) :=
  fun M ↦ Continuous (fun gm : G × M.V.toModule ↦
    (show M.V.toModule →L[R] M.V.toModule from M.ρ gm.1) gm.2)

/-- All compact continuous representations, not only finite modules. -/
abbrev Cat := (continuousAction R G).FullSubcategory

end NoncommCompactRepresentation
