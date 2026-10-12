/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Stalk
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Presheaf TopCat TopCat.Presheaf PresheafOfModules TopologicalSpace

universe u

section

/- The site-generic direct-image functor is the reusable mathlib owner, including for modules over
possibly noncommutative ring presheaves. -/
recall PresheafOfModules.pushforward₀

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (𝒪 : X.Presheaf CommRingCat.{u})

/- Lemma 6.24.1: under the Stacks convention that rings are commutative with `1`, direct image
sends presheaves of `𝒪`-modules functorially to presheaves of `f_* 𝒪`-modules. -/
@[stacks 008S "direct image of presheaves of modules along a continuous map"]
#check
  (PresheafOfModules.pushforward₀ (Opens.map f) (ringPresheafOfComm 𝒪) :
    PresheafOfModules (ringPresheafOfComm 𝒪) ⥤
      PresheafOfModules (ringPresheafOfComm ((pushforward CommRingCat f).obj 𝒪)))

end
