/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Invertible
public import ReasLib.CategoryTheory.ObjectProperty.Representatives
import Mathlib.Tactic.CrossRefAttribute

/-!
# Smallness of invertible module sheaves

Invertibility is the canonical `MonoidalCategory.isInvertibleObject` property.  This leaf records
only the universe-level smallness fact needed to extract representatives; the extraction itself
is owned for arbitrary object properties.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable (O : Sheaf J CommRingCat.{w})
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Invertible module sheaves form an essentially small object property at the natural universe
of the module-sheaf category. -/
@[stacks 040B "essential smallness"]
instance invertibleObjects_essentiallySmall :
    ObjectProperty.EssentiallySmall.{max u v w + 1}
      (MonoidalCategory.isInvertibleObject
        (C := ringedSiteModuleCategory.{u, v, w, w} J O)) := sorry

end SheafOfModules.RingedSite
