/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Homology.CochainComplex.InjectiveResolution.Functorial
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Lemma 13.24.1 (Stacks 0141): a functorial injective embedding gives a strict functor from
bounded-below cochain complexes to injective-resolution arrows, whose source projection is the
identity. This is represented by `CochainComplex.FunctorialInjectiveResolution`, rather than by
the obsolete chapter-local `ResolutionFunctorOne` alias. -/
@[stacks 0141] #check @CochainComplex.FunctorialInjectiveResolution.nonempty

#check @CochainComplex.InjRes
#check @CochainComplex.InjRes.source
