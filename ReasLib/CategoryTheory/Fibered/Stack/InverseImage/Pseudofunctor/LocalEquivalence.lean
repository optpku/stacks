/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.LocalProperties
public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Pseudofunctor.Computations
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local equivalence of the inverse-image pseudofunctor

Under the standard hypotheses on a morphism of sites, the explicitly selected inverse-image
pseudofunctor induces an equivalence on every Hom category.
-/

@[expose] public section

universe uC uD vC vD w₀ w₁

namespace CategoryTheory

open Limits
open scoped Bicategory

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace StackOver.InverseImage

variable (u : C ⥤ D)
variable [HasFiniteLimits C] [PreservesFiniteLimits u]

/-- Under the standard finite-limit and site hypotheses, the selected inverse-image
pseudofunctor induces equivalences on all Hom categories. -/
@[stacks 04WS "inverse image is locally an equivalence"]
instance pseudofunctor.isLocallyEquivalence
    [h_continuous : u.IsContinuous J K] [h_cocontinuous : u.IsCocontinuous J K]
    [h_full : u.Full] [h_faithful : u.Faithful]
    (h : CoherentPseudofunctorChoice.{uC, uD, vC, vD, w₀, w₁}
      (J := J) (K := K) u) :
    (pseudofunctor u h).IsLocallyEquivalence := sorry

end StackOver.InverseImage

end CategoryTheory
