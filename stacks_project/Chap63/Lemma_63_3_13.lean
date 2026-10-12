/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap63.Lemma_63_3_13_LowerShriek

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Lemma 63.3.13: if `f : X ⟶ Y` and `g : Y ⟶ Z` are composable morphisms of
schemes that are separated and locally of finite type, and `F` is an abelian
sheaf on `X_étale`, then `g_! (f_! F) = (f ≫ g)_! F` as subsheaves of
`(f ≫ g)_* F`. -/
@[stacks 0F50]
theorem etaleLowerShriek_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (W : Z.Etale) :
    compactSupportSections (f ≫ g) F W =
      etaleLowerShriekCompSections f g F W :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
