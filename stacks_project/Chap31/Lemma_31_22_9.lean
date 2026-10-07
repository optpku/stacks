module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Smooth

open CategoryTheory

universe u

/- Lemma 31.22.9 (1): in a commutative triangle `Y -i-> X -f-> S` and `Y -j-> S`,
if `f` is smooth, `i` is an immersion, and `j` is a regular immersion, then `i` is a regular
immersion. -/
@[stacks 067S] #check
  (AlgebraicGeometry.isRegularImmersion_of_isRegularImmersion_over_smooth :
    ∀ {Y X S : AlgebraicGeometry.Scheme.{u}}
      (i : Y ⟶ X) (j : Y ⟶ S) (f : X ⟶ S)
      [AlgebraicGeometry.IsImmersion i] [AlgebraicGeometry.Smooth f]
      [AlgebraicGeometry.IsRegularImmersion j],
      i ≫ f = j → AlgebraicGeometry.IsRegularImmersion i)

/- Lemma 31.22.9 (2): in a commutative triangle `Y -i-> X -f-> S` and `Y -j-> S`,
if `f` is smooth, `i` is an immersion, and `j` is a Koszul-regular immersion, then `i` is a
Koszul-regular immersion. -/
@[stacks 067S] #check
  (AlgebraicGeometry.isKoszulRegularImmersion_of_isKoszulRegularImmersion_over_smooth :
    ∀ {Y X S : AlgebraicGeometry.Scheme.{u}}
      (i : Y ⟶ X) (j : Y ⟶ S) (f : X ⟶ S)
      [AlgebraicGeometry.IsImmersion i] [AlgebraicGeometry.Smooth f]
      [AlgebraicGeometry.IsKoszulRegularImmersion j],
      i ≫ f = j → AlgebraicGeometry.IsKoszulRegularImmersion i)

/- Lemma 31.22.9 (3): in a commutative triangle `Y -i-> X -f-> S` and `Y -j-> S`,
if `f` is smooth, `i` is an immersion, and `j` is an `H₁`-regular immersion, then `i` is an
`H₁`-regular immersion. -/
@[stacks 067S] #check
  (AlgebraicGeometry.isH1RegularImmersion_of_isH1RegularImmersion_over_smooth :
    ∀ {Y X S : AlgebraicGeometry.Scheme.{u}}
      (i : Y ⟶ X) (j : Y ⟶ S) (f : X ⟶ S)
      [AlgebraicGeometry.IsImmersion i] [AlgebraicGeometry.Smooth f]
      [AlgebraicGeometry.IsH1RegularImmersion j],
      i ≫ f = j → AlgebraicGeometry.IsH1RegularImmersion i)

/- Lemma 31.22.9 (4): in a commutative triangle `Y -i-> X -f-> S` and `Y -j-> S`,
if `f` is smooth, `i` is an immersion, and `j` is a quasi-regular immersion, then `i` is a
quasi-regular immersion. -/
@[stacks 067S] #check
  (AlgebraicGeometry.isQuasiRegularImmersion_of_isQuasiRegularImmersion_over_smooth :
    ∀ {Y X S : AlgebraicGeometry.Scheme.{u}}
      (i : Y ⟶ X) (j : Y ⟶ S) (f : X ⟶ S)
      [AlgebraicGeometry.IsImmersion i] [AlgebraicGeometry.Smooth f]
      [AlgebraicGeometry.IsQuasiRegularImmersion j],
      i ≫ f = j → AlgebraicGeometry.IsQuasiRegularImmersion i)
