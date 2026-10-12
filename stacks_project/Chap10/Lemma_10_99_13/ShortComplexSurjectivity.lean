/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import StacksCheckRecall

@[expose] public section

/-!
# Short-complex surjectivity support for Lemma 10.99.13

The formal categorical part of the source argument is already provided by Mathlib: an
isomorphism on the middle term and a monomorphism on the right term identify cycles, an
epimorphism on cycles induces one on homology, and epimorphisms in `ModuleCat` are surjective.

@stack 00MN
-/

@[stacks 00MN "middle/right comparison identifies cycles"]
#check @CategoryTheory.ShortComplex.isIso_cyclesMap_of_isIso_of_mono'

@[stacks 00MN "epimorphic cycles comparison gives epimorphic homology"]
#check @CategoryTheory.ShortComplex.epi_homologyMap_of_epi_cyclesMap'

@[stacks 00MN "epimorphisms of modules are surjective"]
#check @ModuleCat.epi_iff_surjective
