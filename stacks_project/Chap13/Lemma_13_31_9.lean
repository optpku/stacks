/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Homology.CochainComplex.KInjective.Adjunction
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.31.9

The reusable statement is owned by the K-injective property.  The supporting
complex map is separately owned by exact adjunctions, so applications retain
only an adjunction and exactness rather than proof-local additive instances.
-/

/- Lemma 13.31.9 (Stacks 08BJ): the right adjoint of an exact functor sends
K-injective cochain complexes to K-injective cochain complexes. -/
@[stacks 08BJ] #check @CochainComplex.IsKInjective.map_of_exactLeftAdjoint

/- Standard-functor bridge for applications that already have an additive right adjoint. -/
@[stacks 08BJ] #check
  @CochainComplex.IsKInjective.mapHomologicalComplex_of_exactLeftAdjoint

/- Supporting neutral API: the right adjoint of an exact functor acts on
homological complexes without extra ambient additive assumptions. -/
@[stacks 08BJ] #check
  @CategoryTheory.Adjunction.Exact.mapHomologicalComplex
