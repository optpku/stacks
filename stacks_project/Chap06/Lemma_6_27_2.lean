/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Skyscraper
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Set TopCat TopologicalSpace

universe u v

noncomputable section

section

variable {X : TopCat.{u}} (x : X)
variable {C : Type v} [Category.{u} C] [HasTerminal C] [HasColimits C] (A : C)

/- Lemma 6.27.2 (1): for a specialization `x ⤳ x'`, the stalk at `x'` of the skyscraper sheaf
at `x` with value `A` is canonically isomorphic to `A`. -/
@[stacks 009B "stalk over a specialization"]
#check TopCat.Sheaf.Skyscraper.stalkIsoOfSpecializes x A

/- Lemma 6.27.2 (2): if `x` does not specialize to `x'`, then the stalk at `x'` of the
skyscraper sheaf at `x` with value `A` is canonically isomorphic to a terminal object. -/
@[stacks 009B "terminal stalk away from the closure"]
#check TopCat.Sheaf.Skyscraper.stalkIsoOfNotSpecializes x A

end

namespace AlgebraicGeometry

section

variable {X : RingedSpace.{u}} (x : X)
variable (M : ModuleCat.{u} (RingCat.of (X.presheaf.stalk x)))
variable {x' : X} (h : x ⤳ x')

/- Lemma 6.27.2 (3): for a specialization `x ⤳ x'`, the stalk at `x'` of the skyscraper module
sheaf attached to `M` is canonically the restriction of `M` along the specialization map. -/
@[stacks 009B "module stalk over a specialization"]
#check asIso (RingedSpace.Module.Skyscraper.stalkMapOfSpecializes x M h)

/- Lemma 6.27.2 (4): if `x` does not specialize to `x'`, the stalk at `x'` of the skyscraper
module sheaf attached to `M` is the zero module over `X.presheaf.stalk x'`. -/
@[stacks 009B "zero module stalk away from the closure"]
#check RingedSpace.Module.Skyscraper.stalk_isZero_of_notSpecializes x M

end

end AlgebraicGeometry
