/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import Mathlib.RingTheory.LocalRing.Basic
public import ReasLib.Algebra.Category.Ring.Sheaf.LocallyRinged
public import ReasLib.Algebra.Category.Ring.Sheaf.Point
import Mathlib.Tactic.CrossRefAttribute

/-!
# Point criteria for locally ringed sheaves

These statements separate the two ingredients of a locally ringed sheaf.  Local unit dichotomy
is detected by the zero-or-local alternative on stalks, while local nontriviality is detected by
nontriviality of the stalk rings.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u v

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (𝒪 : Sheaf J CommRingCat.{max u v})

section UnitDichotomy

/-- Local unit dichotomy forces every point stalk to be either the zero ring or a local ring. -/
@[stacks 04ET "(1)"]
theorem LocalUnitDichotomy.stalk_zero_or_local [𝒪.LocalUnitDichotomy]
    (p : GrothendieckTopology.Point.{max u v} J) :
    Subsingleton (p.stalkCommRing 𝒪) ∨ IsLocalRing (p.stalkCommRing 𝒪) := sorry

/-- On a site with enough points, local unit dichotomy is detected by the zero-or-local
alternative for all point stalks. -/
@[stacks 04ET "(2)"]
theorem localUnitDichotomy_iff_stalk_zero_or_local
    [GrothendieckTopology.HasEnoughPoints.{max u v} J] :
    𝒪.LocalUnitDichotomy ↔
      ∀ p : GrothendieckTopology.Point.{max u v} J,
        Subsingleton (p.stalkCommRing 𝒪) ∨ IsLocalRing (p.stalkCommRing 𝒪) := sorry

end UnitDichotomy

section Nontriviality

variable [HasWeakSheafify J (Type (max u v))]
variable [J.HasSheafCompose (forget CommRingCat.{max u v})]

/-- Local nontriviality makes every point stalk nontrivial. -/
@[stacks 05D8 "(1)"]
theorem nontrivial_stalk [IsIso 𝒪.nontrivialityMap]
    (p : GrothendieckTopology.Point.{max u v} J) :
    Nontrivial (p.stalkCommRing 𝒪) := sorry

/-- On a site with enough points, local nontriviality is detected by nontriviality of all point
stalks. -/
@[stacks 05D8 "(2)"]
theorem nontrivialityMap_isIso_iff_stalk_nontrivial
    [GrothendieckTopology.HasEnoughPoints.{max u v} J] :
    IsIso 𝒪.nontrivialityMap ↔
      ∀ p : GrothendieckTopology.Point.{max u v} J,
        Nontrivial (p.stalkCommRing 𝒪) := sorry

/-- Every point stalk of a locally ringed sheaf is a local ring. -/
@[stacks 04H9 "local stalk rings"]
instance IsLocallyRinged.stalk_isLocalRing [𝒪.IsLocallyRinged]
    (p : GrothendieckTopology.Point.{max u v} J) :
    IsLocalRing (p.stalkCommRing 𝒪) := sorry

end Nontriviality

end CategoryTheory.Sheaf
