/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Depth.Exact
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.72.6

@stack 00LX

The depth lemma gives the three symmetric depth inequalities associated to a short exact sequence
of nonzero finite modules over a Noetherian local ring. The canonical owner proves a stronger
version, but the tagged recalls below retain the source context.
-/

open CategoryTheory

universe u v

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {S : ShortComplex (ModuleCat.{v} R)}
variable [Module.Finite R S.X₁] [Module.Finite R S.X₂] [Module.Finite R S.X₃]
variable [Nontrivial S.X₁] [Nontrivial S.X₂] [Nontrivial S.X₃]
variable (hS : S.ShortExact)

/- Lemma 10.72.6 (1): the middle term has depth at least the minimum of the endpoint depths. -/
@[stacks 00LX "(1), middle term"]
#check CategoryTheory.ShortComplex.ShortExact.moduleDepth_middle_ge_min hS

/- Lemma 10.72.6 (2): the quotient has depth at least the minimum of the middle depth and the
predecessor of the submodule depth. -/
@[stacks 00LX "(2), quotient term"]
#check CategoryTheory.ShortComplex.ShortExact.moduleDepth_right_ge_min hS

/- Lemma 10.72.6 (3): the submodule has depth at least the minimum of the middle depth and the
successor of the quotient depth. -/
@[stacks 00LX "(3), submodule term"]
#check CategoryTheory.ShortComplex.ShortExact.moduleDepth_left_ge_min hS

end
