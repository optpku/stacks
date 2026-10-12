/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

variable (A : CommRingCat.{u})

/- Definition 46.3.1 (1): a module-valued functor on `A`-algebras assigns a
`B`-module to every `A`-algebra `B`, with functorial transition maps that are
`B`-linear after restriction of scalars. -/
@[stacks 06Z4] #check (ModuleValuedFunctor.{u, v} A : Type (max (u + 1) (v + 1)))

variable (F G : ModuleValuedFunctor.{u, v} A)

/- Definition 46.3.1 (2): a morphism of module-valued functors is a natural
transformation whose component over every `A`-algebra `B` is `B`-linear. -/
@[stacks 06Z4] #check (ModuleValuedFunctor.Hom F G : Type (max (u + 1) v))
