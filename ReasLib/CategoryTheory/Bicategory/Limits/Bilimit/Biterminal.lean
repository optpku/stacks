/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid
public import ReasLib.CategoryTheory.Bicategory.Biterminal
public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Basic

/-!
# Bilimits as biterminal pseudocones

In a locally groupoidal bicategory, the represented Yoneda universal property of a conical
bilimit is equivalent to biterminality in the bicategory of varying-apex pseudocones.

This bridge belongs directly above the basic bilimit owner: it does not require chosen
universal lifts, their functoriality, or a comparison between two selected bilimit apices.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u wJ vJ uJ

namespace CategoryTheory

open Bicategory

namespace Bicategory.PseudoCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {J : Type uJ} [Bicategory.{wJ, vJ} J]
variable {F : J ⥤ᵖ B}

/-- In a locally groupoidal bicategory, a varying-apex pseudocone is biterminal exactly when
its represented comparison functors exhibit it as a bilimit cone. -/
theorem isBiterminal_iff_isBilimit [IsLocallyGroupoid B] (S : PseudoCone F) :
    Bicategory.IsBiterminal S ↔ S.IsBilimit := sorry

/-- A bilimit pseudocone in a locally groupoidal bicategory is biterminal in the bicategory
of varying-apex pseudocones. -/
theorem isBiterminal_of_isBilimit [IsLocallyGroupoid B]
    (S : PseudoCone F) [S.IsBilimit] :
    Bicategory.IsBiterminal S := sorry

/-- A biterminal varying-apex pseudocone in a locally groupoidal bicategory satisfies the
represented bilimit universal property. -/
theorem isBilimit_of_isBiterminal [IsLocallyGroupoid B]
    (S : PseudoCone F) [Bicategory.IsBiterminal S] :
    S.IsBilimit := sorry

end Bicategory.PseudoCone

end CategoryTheory
