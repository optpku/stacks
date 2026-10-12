/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.PureInjective.Resolution.PureExt
import StacksCheckRecall

universe u v

/- Definition 46.8.8: for a chosen pure injective resolution `I` of `N`, the pure extension
module in degree `i` is the degree-`i` cohomology of `Hom_A(M, I)`. -/
@[stacks 0705] #check
  (ModuleCat.PureInjectiveCoresolution.pureExt :
    ∀ {A : Type u} [CommRing A] {N : ModuleCat.{v} A},
      ModuleCat.PureInjectiveCoresolution N → ModuleCat.{v} A → ℕ → ModuleCat.{v} A)
