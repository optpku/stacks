module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Smooth

open CategoryTheory

universe u

/- Lemma 31.22.12 (1): postcomposition with a smooth morphism preserves
Koszul-regularity when the composite is an immersion. -/
@[stacks 0693] #check
  (AlgebraicGeometry.isKoszulRegularImmersion_of_isKoszulRegularImmersion_comp_smooth :
    ∀ {Y X S : AlgebraicGeometry.Scheme.{u}} (i : Y ⟶ X) (j : Y ⟶ S) (f : X ⟶ S)
      [AlgebraicGeometry.IsImmersion j] [AlgebraicGeometry.Smooth f]
      [AlgebraicGeometry.IsKoszulRegularImmersion i],
      i ≫ f = j → AlgebraicGeometry.IsKoszulRegularImmersion j)

/- Lemma 31.22.12 (2): postcomposition with a smooth morphism preserves
`H₁`-regularity when the composite is an immersion. -/
@[stacks 0693] #check
  (AlgebraicGeometry.isH1RegularImmersion_of_isH1RegularImmersion_comp_smooth :
    ∀ {Y X S : AlgebraicGeometry.Scheme.{u}} (i : Y ⟶ X) (j : Y ⟶ S) (f : X ⟶ S)
      [AlgebraicGeometry.IsImmersion j] [AlgebraicGeometry.Smooth f]
      [AlgebraicGeometry.IsH1RegularImmersion i],
      i ≫ f = j → AlgebraicGeometry.IsH1RegularImmersion j)

/- Lemma 31.22.12 (3): postcomposition with a smooth morphism preserves
quasi-regularity when the composite is an immersion. -/
@[stacks 0693] #check
  (AlgebraicGeometry.isQuasiRegularImmersion_of_isQuasiRegularImmersion_comp_smooth :
    ∀ {Y X S : AlgebraicGeometry.Scheme.{u}} (i : Y ⟶ X) (j : Y ⟶ S) (f : X ⟶ S)
      [AlgebraicGeometry.IsImmersion j] [AlgebraicGeometry.Smooth f]
      [AlgebraicGeometry.IsQuasiRegularImmersion i],
      i ≫ f = j → AlgebraicGeometry.IsQuasiRegularImmersion j)
