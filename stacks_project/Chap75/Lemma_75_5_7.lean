/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Lower.Comparison

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.DerivedCategory.Truncation

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 75.5.7: let `S` be a scheme, let `X` be an algebraic space over `S`, and
let `E` be an object of `DerivedQCoh X`. Then every Remark 13.34.5 compatible map
`c : E.obj ⟶ K` from `E` to a derived limit of `n ↦ τ≥(-n) E` is an isomorphism. -/
@[stacks 08F6]
theorem lowerTruncationComparison_isIso {S : Scheme.{u}} {X : AlgebraicSpace S}
    (E : DerivedQCoh X) {K : ModuleDerived X} {c : E.obj ⟶ K}
    (hc : Lower.Comparison.Exists E.obj c) :
    IsIso c := sorry

end AlgebraicGeometry.AlgebraicSpace
