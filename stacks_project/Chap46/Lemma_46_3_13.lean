/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Linearity
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace ModuleValuedFunctor

variable {A : CommRingCat.{u}} {F G : ModuleValuedFunctor.{u, u} A}

/- Lemma 46.3.13: an additive transformation of module-valued functors that commutes with
units is a morphism of module-valued functors when the target has flat base change. -/
@[stacks 06V5]
#check
  (ModuleValuedFunctor.Hom.ofUnitCompatibleOfFlatBaseChange_toNatTrans :
    ∀ (φ : F.toFunctor ⟶ G.toFunctor)
      (h_units : ModuleValuedFunctor.RespectsUnitScalars φ)
      (h_flat : ModuleValuedFunctor.HasFlatBaseChange G),
      (ModuleValuedFunctor.Hom.ofUnitCompatibleOfFlatBaseChange φ h_units h_flat).toNatTrans = φ)

end ModuleValuedFunctor
