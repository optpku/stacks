/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_21_3_Comparison
import StacksCheckRecall

/-!
# Comparison of the naive cotangent complex of algebraic spaces with schemes

A morphism of algebraic spaces over a scheme `S` that is representable by a morphism
of schemes has naive cotangent complex identified in `D(𝒪_X)` with the inverse image
along `ε` of the scheme-level naive cotangent complex.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom.NaiveCotangent
open scoped AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.21.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic spaces
over `S`. Assume `X` and `Y` representable by schemes `X0` and `Y0`. Then there is a
canonical identification `NL[X/Y] = ε* NL[X0/Y0]` in `D(𝒪_X)`, where `ε` is as in
Section 75.4 and `NL[X0/Y0]` is the scheme-level naive cotangent complex. -/
@[stacks 0D0X] #check ofOverHomIso_derived
