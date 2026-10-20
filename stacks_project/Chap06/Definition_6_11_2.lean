/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.Types.Sheafification
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace TopCat.Presheaf

variable {X : TopCat.{u}} (ℱ : X.Presheaf (Type u))

/- The canonical owner for separated presheaves is the site-theoretic predicate
`Presieve.IsSeparated`; the concrete stalk-family criterion is its source-facing bridge. -/

/- The canonical owner for separated set-valued presheaves is `Presieve.IsSeparated`. -/
recall Presieve.IsSeparated

/- Definition 6.11.2: a set-valued presheaf on `X` is separated, in the canonical site-theoretic
sense for `Opens.grothendieckTopology X`, if and only if for every open subset `U` the canonical
map from sections on `U` to the family of germs in the stalks over points of `U` is injective. -/
@[stacks 007A]
#check isSeparated_iff_injective_toStalkFamily ℱ

end TopCat.Presheaf
