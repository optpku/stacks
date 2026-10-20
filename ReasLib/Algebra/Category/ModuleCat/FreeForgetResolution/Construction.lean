/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Adjunction.SimplicialResolution.Construction
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions

/-!
# Constructing the free-forgetful resolution of modules

This leaf specializes the canonical adjunction resolution to the free-forgetful adjunction on
`ModuleCat R`. It owns the comonad, its augmented simplicial resolution, its evaluated and
underlying views, and their degreewise descriptions.
-/

@[expose] public section

open Opposite
open CategoryTheory
open CategoryTheory.SimplicialObject
open scoped Simplicial CategoryTheory.IteratedEndofunctor

universe u

namespace CategoryTheory.ModuleCat.FreeForgetResolution

variable (R : Type u) [Ring R]

/-- The comonad on `ModuleCat R` induced by the free-forgetful adjunction. -/
@[stacks 0G5T "free-forgetful comonad"]
noncomputable abbrev comonad : Comonad (ModuleCat R) := (ModuleCat.adj R).toComonad

/-- The endofunctor whose positive iterates form the free-forgetful resolution. -/
@[stacks 0G5U "free-forgetful resolution endofunctor"]
noncomputable abbrev functor : ModuleCat R ⥤ ModuleCat R := (comonad R).toFunctor

/-- The counit of the free-forgetful comonad. -/
@[stacks 0G5T "free-forgetful counit"]
noncomputable abbrev counit : functor R ⟶ 𝟭 (ModuleCat R) := (comonad R).ε

/-- The comultiplication of the free-forgetful comonad. -/
@[stacks 0G5U "free-forgetful comultiplication"]
noncomputable abbrev comultiplication : functor R ⟶ functor R ⋙ functor R := (comonad R).δ

/-- The `n`-th iterated face map of the free-forgetful resolution. -/
@[stacks 0G5U "free-forgetful resolution face maps"]
noncomputable abbrev face (n : ℕ) (j : Fin (n + 2)) :
    IteratedEndofunctor.obj (functor R) (n + 1) ⟶ IteratedEndofunctor.obj (functor R) n :=
  IteratedEndofunctor.face (counit R) n j

/-- The `n`-th iterated degeneracy map of the free-forgetful resolution. -/
@[stacks 0G5U "free-forgetful resolution degeneracy maps"]
noncomputable abbrev degeneracy (n : ℕ) (j : Fin (n + 1)) :
    IteratedEndofunctor.obj (functor R) n ⟶ IteratedEndofunctor.obj (functor R) (n + 1) :=
  IteratedEndofunctor.degeneracy (comultiplication R) n j

/-- The canonical augmented simplicial endofunctor resolution for `ModuleCat R`. -/
@[stacks 0G5T "free-forgetful augmented resolution"]
noncomputable abbrev augmented :
    SimplicialObject.Augmented (ModuleCat R ⥤ ModuleCat R) :=
  Comonad.simplicialResolution.augmented (comonad R)

/-- The canonical augmented simplicial module resolution, functorial in the resolved module. -/
@[stacks 0G5T "evaluated free-forgetful resolution functor"]
noncomputable abbrev evaluation : ModuleCat R ⥤ SimplicialObject.Augmented (ModuleCat R) :=
  Adjunction.SimplicialResolution.eval (ModuleCat.adj R)

/- The underlying views of the evaluated free-forgetful resolution. -/
namespace underlying

/-- The evaluated resolution after forgetting functorially to augmented simplicial sets. -/
@[stacks 0G5T "free-forgetful resolution underlying set functor"]
noncomputable abbrev setFunctor :
    ModuleCat R ⥤ SimplicialObject.Augmented (Type u) :=
  Adjunction.SimplicialResolution.postcompose.eval (ModuleCat.adj R)

/-- Forgetting the evaluated free-forgetful resolution degreewise agrees with the canonical
postcomposed adjunction resolution. -/
@[stacks 0G5T "free-forgetful resolution underlying-set comparison"]
theorem setFunctor_eq :
    setFunctor R =
      evaluation R ⋙ SimplicialObject.Augmented.whiskeringObj
        (ModuleCat R) (Type u) (CategoryTheory.forget (ModuleCat R)) := sorry

/-- The evaluated resolution of `M` after forgetting to an augmented simplicial set. -/
@[stacks 0G5T "free-forgetful resolution underlying set view"]
noncomputable abbrev set (M : ModuleCat R) : SimplicialObject.Augmented (Type u) :=
  (setFunctor R).obj M

/-- The evaluated resolution after forgetting functorially to augmented simplicial additive
groups. -/
@[stacks 0G5T "free-forgetful resolution underlying additive-group functor"]
noncomputable abbrev addCommGrpFunctor :
    ModuleCat R ⥤ SimplicialObject.Augmented AddCommGrpCat :=
  evaluation R ⋙ SimplicialObject.Augmented.whiskeringObj (ModuleCat R) AddCommGrpCat
    (forget₂ (ModuleCat R) AddCommGrpCat)

/-- Forgetting the additive-group view degreewise recovers the underlying-set resolution. -/
@[stacks 0G5T "underlying additive-group and set resolution compatibility"]
theorem addCommGrpFunctor_comp_forget :
    addCommGrpFunctor R ⋙ SimplicialObject.Augmented.whiskeringObj
        AddCommGrpCat (Type u) (CategoryTheory.forget AddCommGrpCat) =
      setFunctor R := sorry

/-- The evaluated resolution of `M` after forgetting to an augmented simplicial additive
group. -/
@[stacks 0G5T "free-forgetful resolution underlying additive-group view"]
noncomputable abbrev addCommGrp (M : ModuleCat R) :
    SimplicialObject.Augmented AddCommGrpCat :=
  (addCommGrpFunctor R).obj M

end underlying

/-- Degree `n` of the free-forgetful resolution is the `(n + 1)`-fold comonad iterate. -/
@[stacks 0G5T "free-forgetful resolution degree formula"]
theorem evaluation.obj_eq (M : ModuleCat R) (n : ℕ) :
    ((evaluation R).obj M).left.obj (op ⦋n⦌) =
      (comonad R).toFunctor ⁺⦋n⦌.obj M := sorry

namespace evaluation

/-- The underlying simplicial `R`-module of the evaluated resolution. -/
@[stacks 0G5T "underlying free-forgetful simplicial module"]
noncomputable abbrev simplicial (M : ModuleCat R) : SimplicialObject (ModuleCat R) :=
  ((evaluation R).obj M).left

end evaluation

end CategoryTheory.ModuleCat.FreeForgetResolution
