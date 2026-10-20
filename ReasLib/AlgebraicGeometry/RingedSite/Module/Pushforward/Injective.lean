/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Flat
public import ReasLib.CategoryTheory.Adjunction.Abelian
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat direct image and injective modules

An exact module pullback is left adjoint to module direct image. Consequently, direct image along
a flat morphism preserves injective module sheaves. This leaf exposes both the functorial property
and its objectwise specialization.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe z uX vX uY vY w

namespace RingedSite.Hom.modulePushforward

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}

/-- Lemma 21.14.2 (0730), functorial form: module direct image along a flat morphism preserves
injective objects. -/
@[stacks 0730 "flat direct image preserves injectives"]
instance preservesInjectiveObjects_of_isFlat
    (f : RingedSite.Hom X Y) [(f.modulePushforward.{z}).IsRightAdjoint]
    [IsFlat.{z} f] :
    f.modulePushforward.{z}.PreservesInjectiveObjects := sorry

/-- Lemma 21.14.2 (0730): the direct image of an injective module sheaf is injective; the
objectwise bridge is instance-driven so callers can use the standard `Injective` API. -/
@[stacks 0730]
theorem injective_obj_of_isFlat
    (f : RingedSite.Hom X Y) [(f.modulePushforward.{z}).IsRightAdjoint]
    [IsFlat.{z} f] (I : ModuleCat.{z} X) [Injective I] :
    Injective (f.modulePushforward.obj I) := sorry

end RingedSite.Hom.modulePushforward
