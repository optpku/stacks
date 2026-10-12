/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

@[expose] public section

universe u

open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/-- Two morphisms to a separated scheme over a base are equal if they agree after
precomposition with a scheme-theoretically dominant morphism. -/
theorem ext_of_isSchemeTheoreticallyDominant_of_isSeparated'
    {S X Y W : Scheme.{u}} [X.Over S] [Y.Over S] (ι : W ⟶ X)
    {f g : X ⟶ Y} [f.IsOver S] [g.IsOver S] [IsSeparated (Y ↘ S)]
    [IsSchemeTheoreticallyDominant ι] (h : ι ≫ f = ι ≫ g) :
    f = g := sorry

end AlgebraicGeometry

end
