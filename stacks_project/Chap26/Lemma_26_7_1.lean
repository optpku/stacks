/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.Adjunction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

variable (R : CommRingCat.{u}) (M : ModuleCat R)

/- Lemma 26.7.1: affine module sheafification, its functoriality, quasi-coherence, and its
adjunction with global sections are the canonical tilde API. -/
@[stacks 01I7] #check tilde.functor
@[stacks 01I7] #check tilde
@[stacks 01I7] #check tilde.map
@[stacks 01I7] #check (inferInstance : (tilde M).IsQuasicoherent)
@[stacks 01I7] #check tilde.associatedFunctorIso
@[stacks 01I7] #check tilde.adjunction
#check tilde.isoTop
@[stacks 01I7] #check tilde.adjunction_homEquiv_apply
