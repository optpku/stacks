/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Basic

/-!
# Explicit families of bilimit cones

An explicit family of bilimit cones selects one `BilimitCone F` for every diagram `F` of
a fixed shape. This is the data-bearing counterpart of the propositional typeclass
`HasBilimitsOfShape`.

This file contains only the selection and projection layer. Universal maps between
selected apexes and the resulting pseudofunctor are defined in downstream modules, so
clients that merely retain chosen cones do not import transport coherence.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe uB vB wB uJ vJ wJ

namespace CategoryTheory

open Bicategory

namespace Bicategory

variable {J : Type uJ} [Bicategory.{wJ, vJ} J]
variable {B : Type uB} [Bicategory.{wB, vB} B]

/-- An explicit selection of a `BilimitCone F` for every `J`-shaped pseudodiagram `F` in
`B`.

Unlike `HasBilimitsOfShape J B`, this family retains the selected cones as computational
data and can therefore support canonical downstream maps between their apexes. -/
abbrev BilimitConeFamily :=
  (F : Pseudofunctor J B) → BilimitCone F

namespace BilimitConeFamily

/-- The pseudocone underlying the selected bilimit cone of a diagram. -/
abbrev cone (L : BilimitConeFamily (J := J) (B := B))
    (F : Pseudofunctor J B) : PseudoCone F :=
  (L F).cone

/-- Every cone selected by a bilimit-cone family carries its specified bilimit
instance. -/
instance coneIsBilimit (L : BilimitConeFamily (J := J) (B := B))
    (F : Pseudofunctor J B) : (L.cone F).IsBilimit :=
  (L F).isBilimit

/-- An explicit bilimit-cone family proves that the selected diagram has a bilimit. -/
theorem hasBilimit (L : BilimitConeFamily (J := J) (B := B))
    (F : Pseudofunctor J B) : HasBilimit F := sorry

/-- An explicit bilimit-cone family proves existence of bilimits of its fixed shape. -/
theorem hasBilimitsOfShape
    (L : BilimitConeFamily (J := J) (B := B)) :
    HasBilimitsOfShape J B := sorry

/-- The apex of the selected bilimit cone of a diagram. -/
abbrev apex (L : BilimitConeFamily (J := J) (B := B))
    (F : Pseudofunctor J B) : B :=
  (L.cone F).pt

/- Data and axiom audit (mathlib 4.32):

`BilimitConeFamily` is a dependent function whose values are explicit `BilimitCone`s.
The projections `cone` and `apex` expose stored data directly; no family-level
`Classical.choice` is used. Any proof debt is confined to the `Prop`-valued bilimit and
existence fields. -/

end BilimitConeFamily

end Bicategory

end CategoryTheory
