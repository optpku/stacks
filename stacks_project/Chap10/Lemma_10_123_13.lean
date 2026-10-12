/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Affine
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.123.13: for a finite-type ring map `R → S`, the quasi-finite locus in `Spec(S)` is open.
The companion pointwise bridge identifies the scheme-theoretic and ring-theoretic predicates.

The reusable owner is `AlgebraicGeometry.Scheme.Hom` in
`ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Affine`.

@stack 00QA
-/
@[stacks 00QA "affine pointwise quasi-finite bridge"]
#check @AlgebraicGeometry.Scheme.Hom.specMap_quasiFiniteAt_iff

@[stacks 00QA "affine quasi-finite locus open"]
#check @AlgebraicGeometry.Scheme.Hom.isOpen_setOf_quasiFiniteAt
