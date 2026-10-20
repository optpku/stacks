/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Point.Over
public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fibers of localization direct image at a point

Unlike localization lower shriek, localization direct image has no uniform
fiberwise sigma decomposition over localized points.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.GrothendieckTopology.Point.Localization.Pushforward

/-- There is no uniform sigma decomposition of the point fiber of localization direct image by
the fibers at localized points. -/
@[stacks 04H5, stacks 0711 "underlying-sheaf obstruction"]
theorem not_forall_sheafFiber_isomorphic_sigma :
    ¬ ∀ {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [LocallySmall.{max u v} C]
        (U : C) (p : Point.{max u v} J) (G : Sheaf (J.over U) (Type (max u v))),
        IsIsomorphic
          (p.sheafFiber.obj
            (((Over.forget U).sheafPushforwardCocontinuous
              (Type (max u v)) (J.over U) J).obj G))
          (Σ x : p.fiber.obj U, (p.over x).sheafFiber.obj G) := sorry

end CategoryTheory.GrothendieckTopology.Point.Localization.Pushforward
