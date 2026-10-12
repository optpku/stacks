/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Coskeleton.Limits
import StacksCheckRecall

/-!
@stack 018D

# Lemma 14.19.13 compatibility facade

The reusable owner is ReasLib's objectwise coskeleton pullback comparison.  The tagged source
entry retains the ambient pullback hypothesis, while an untagged companion records the sharper
single-cospan interface.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.SimplicialObject

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {n : ℕ}
variable [HasPullbacks C]
variable {U V W : SimplicialObject.Truncated C n}
variable (f : U ⟶ V) (g : W ⟶ V)
variable [U.HasCoskeleton] [V.HasCoskeleton] [W.HasCoskeleton]
variable [(pullback f g).HasCoskeleton]

/- Lemma 14.19.13: the `n`-coskeleton functor preserves the pullback of `f` and `g`. -/
@[stacks 018D]
#check (Truncated.coskeleton.pullback.iso f g :
  (pullback f g).coskeleton ≅
    pullback (Truncated.coskeleton.map f) (Truncated.coskeleton.map g))

/- The forward and inverse projection formulas characterize the canonical pullback comparison. -/
#check Truncated.coskeleton.pullback.iso_hom_fst f g
#check Truncated.coskeleton.pullback.iso_hom_snd f g
#check Truncated.coskeleton.pullback.iso_inv_fst f g
#check Truncated.coskeleton.pullback.iso_inv_snd f g

section Objectwise

variable {C' : Type u} [Category.{v} C'] {m : ℕ}
variable {U' V' W' : SimplicialObject.Truncated C' m}
variable (f' : U' ⟶ V') (g' : W' ⟶ V') [HasPullback f' g']
variable [U'.HasCoskeleton] [V'.HasCoskeleton] [W'.HasCoskeleton]
variable [(pullback f' g').HasCoskeleton]
variable [HasPullback (Truncated.coskeleton.map f') (Truncated.coskeleton.map g')]

/- The same comparison only needs the particular source and target pullbacks involved. -/
#check (Truncated.coskeleton.pullback.iso f' g' :
  (pullback f' g').coskeleton ≅
    pullback (Truncated.coskeleton.map f') (Truncated.coskeleton.map g'))

end Objectwise

end CategoryTheory
