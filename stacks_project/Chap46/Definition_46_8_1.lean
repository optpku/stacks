/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Pure
import StacksCheckRecall

@[expose] public section

universe u v

variable {R : Type u} [CommRing R]

/- Definition 46.8.1 (1): a module is pure projective when covariant Hom out of it sends every
universally exact sequence to a short exact sequence. -/
@[stacks 06ZY] #check (ModuleCat.PureProjective : ModuleCat.{v} R → Prop)

/- Definition 46.8.1 (2): a module is pure injective when contravariant Hom into it sends every
universally exact sequence to a short exact sequence in the reverse direction. -/
@[stacks 06ZY] #check (ModuleCat.PureInjective : ModuleCat.{v} R → Prop)
