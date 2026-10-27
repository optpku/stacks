/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RegularImmersion.Implications
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Transitivity.Splitting

/-!
# Permanence of regular immersions along split conormal transitivity

For composable immersions of algebraic spaces, locally split conormal
transitivity allows regularity of the composite to descend to the first
morphism under the appropriate finite-presentation hypotheses.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open Hom.Conormal.Transitivity

namespace IsQuasiRegularImmersion

/-- If the second immersion is locally of finite presentation and the canonical
conormal transitivity sequence is locally split, quasi-regularity of the
composite implies quasi-regularity of the first immersion. -/
theorem of_comp_of_split_conormal
    {S : Scheme.{u}} {Z Y X : AlgebraicSpace S} (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion j] [LocallyOfFinitePresentation j]
    (hconormal : IsShortExactLocallySplit i j)
    [IsQuasiRegularImmersion (i ≫ j)] :
    IsQuasiRegularImmersion i :=
  sorry

end IsQuasiRegularImmersion

namespace IsH1RegularImmersion

/-- If the second immersion is locally of finite presentation and the canonical
conormal transitivity sequence is locally split, `H₁`-regularity of the
composite implies `H₁`-regularity of the first immersion. -/
theorem of_comp_of_split_conormal
    {S : Scheme.{u}} {Z Y X : AlgebraicSpace S} (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion j] [LocallyOfFinitePresentation j]
    (hconormal : IsShortExactLocallySplit i j)
    [IsH1RegularImmersion (i ≫ j)] :
    IsH1RegularImmersion i :=
  sorry

end IsH1RegularImmersion

namespace IsKoszulRegularImmersion

/-- If the second immersion and the composite are Koszul-regular and the
canonical conormal transitivity sequence is locally split, then the first
immersion is Koszul-regular. -/
theorem of_comp_of_split_conormal
    {S : Scheme.{u}} {Z Y X : AlgebraicSpace S} (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [LocallyOfFinitePresentation j] [IsKoszulRegularImmersion j]
    (hconormal : IsShortExactLocallySplit i j)
    [IsKoszulRegularImmersion (i ≫ j)] :
    IsKoszulRegularImmersion i :=
  sorry

end IsKoszulRegularImmersion

end AlgebraicGeometry.AlgebraicSpace
