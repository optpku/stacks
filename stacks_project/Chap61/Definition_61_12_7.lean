/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 61.12.7: a big pro-étale site is a chosen small category of schemes
with arbitrary seed schemes and seed pro-étale coverings, closed under the
bound Scheme.proetaleBound, with countable limits and colimits agreeing with
Scheme and a pretopology representing the pro-étale coverings on that category. -/
@[stacks 098G] #check (AlgebraicGeometry.BigProetaleSite.{u} : Type (u + 1))
