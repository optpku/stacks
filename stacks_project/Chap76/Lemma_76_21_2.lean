/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_21_2_Comparison
import StacksCheckRecall

/-!
# Étale localization of the naive cotangent complex of algebraic spaces

A commutative square of algebraic spaces over a scheme `S` with étale vertical arrows
yields a canonical identification of naive cotangent complexes in `D(𝒪_U)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.Hom.NaiveCotangent
open AlgebraicGeometry.AlgebraicSpace.Modules
open ComplexShape
open scoped AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.21.2: Let `S` be a scheme. Consider a commutative diagram of algebraic spaces
over `S` with étale vertical arrows `p : U ⟶ X` and `q : V ⟶ Y`. Then there is a canonical
identification `NL[f]|_{U_étale} = NL[g]` in `D(𝒪_U)`. -/
@[stacks 0D0W] #check etaleRestrictIso_derived
