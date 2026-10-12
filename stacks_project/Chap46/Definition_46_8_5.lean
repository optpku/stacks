/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.PureInjective.Resolution
public import ReasLib.Algebra.Category.ModuleCat.PureProjective.Resolution
import StacksCheckRecall

universe u v

/- Definition 46.8.5 (1): a pure projective resolution is an augmented nonnegative chain
complex of pure projective modules that is universally exact at every degree. -/
@[stacks 0702] #check
  (ModuleCat.PureProjectiveResolution :
    {A : Type u} → [CommRing A] → (M : ModuleCat.{v} A) → Type (max u (v + 1)))

/- Definition 46.8.5 (2): a pure injective resolution is an augmented nonnegative cochain
complex of pure injective modules that is universally exact at every degree. -/
@[stacks 0702] #check
  (ModuleCat.PureInjectiveCoresolution :
    {A : Type u} → [CommRing A] → (N : ModuleCat.{v} A) → Type (max u (v + 1)))
