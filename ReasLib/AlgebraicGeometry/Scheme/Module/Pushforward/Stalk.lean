module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Topology.Sheaves.Stalks
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition

/-!
# Stalks of pushforward modules

This file defines the canonical map from the stalk of a pushforward module to the original
stalk after restriction of scalars and records a singleton-fiber criterion for this map to be an
isomorphism.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The additive stalk map from a pushforward module is semilinear for the local-ring map
induced by the scheme morphism. -/
theorem stalkPushforward_smul {X Y : Scheme.{u}} (f : X ⟶ Y) (ℱ : X.Modules) (x : X)
    (r : Y.presheaf.stalk (f x))
    (m : RingedSpace.stalkModuleCat ((pushforward f).obj ℱ) (f x)) :
    TopCat.Presheaf.stalkPushforward AddCommGrpCat f.base ℱ.val.presheaf x (r • m) =
      (f.stalkMap x).hom r •
        TopCat.Presheaf.stalkPushforward AddCommGrpCat f.base ℱ.val.presheaf x m := sorry

/-- The canonical map from the stalk of a pushed-forward scheme module to the original stalk,
viewed after restriction of scalars along the local-ring map. -/
noncomputable def stalkPushforward {X Y : Scheme.{u}} (f : X ⟶ Y) (ℱ : X.Modules) (x : X) :
    RingedSpace.stalkModuleCat ((pushforward f).obj ℱ) (f x) ⟶
      (ModuleCat.restrictScalars (f.stalkMap x).hom).obj
        (RingedSpace.stalkModuleCat ℱ x) :=
  (ModuleCat.semilinearMapAddEquiv (f.stalkMap x).hom
    (RingedSpace.stalkModuleCat ((pushforward f).obj ℱ) (f x))
    (RingedSpace.stalkModuleCat ℱ x))
    { toFun := TopCat.Presheaf.stalkPushforward AddCommGrpCat f.base ℱ.val.presheaf x
      map_add' :=
        (TopCat.Presheaf.stalkPushforward AddCommGrpCat f.base ℱ.val.presheaf x).hom.map_add
      map_smul' := stalkPushforward_smul f ℱ x }

/-- The underlying function of `stalkPushforward` is the usual presheaf stalk-pushforward map. -/
@[simp]
theorem stalkPushforward_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (ℱ : X.Modules) (x : X)
    (m : RingedSpace.stalkModuleCat ((pushforward f).obj ℱ) (f x)) :
    stalkPushforward f ℱ x m =
      TopCat.Presheaf.stalkPushforward AddCommGrpCat f.base ℱ.val.presheaf x m := sorry

/-- The module stalk-pushforward map is an isomorphism at a point when the underlying map is
closed and that point is the unique point of its fiber. -/
theorem stalkPushforward_isIso_of_isClosedMap_of_fiber_eq_singleton
    {X Y : Scheme.{u}} (f : X ⟶ Y) (ℱ : X.Modules) (x : X)
    (h_closed : IsClosedMap f) (h_fiber : f ⁻¹' {f x} = {x}) :
    IsIso (stalkPushforward f ℱ x) := sorry

end AlgebraicGeometry.Scheme.Modules
