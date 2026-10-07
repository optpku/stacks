module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion

open CategoryTheory

universe u

/- Definition 31.21.1 (1): an immersion is regular when it factors through an open subscheme
as a regular closed immersion. -/
@[stacks 063J] #check (@AlgebraicGeometry.IsRegularImmersion :
  ∀ {X Z : AlgebraicGeometry.Scheme.{u}}, (Z ⟶ X) → Prop)

#check (@AlgebraicGeometry.isRegularImmersion_iff :
  ∀ {X Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X),
    AlgebraicGeometry.IsRegularImmersion i ↔
      AlgebraicGeometry.IsImmersion i ∧
        ∃ U : X.Opens, ∃ j : Z ⟶ U.toScheme,
          AlgebraicGeometry.IsRegularClosedImmersion j ∧ j ≫ U.ι = i)

/- Definition 31.21.1 (2): an immersion is Koszul-regular when it factors through an open
subscheme as a Koszul-regular closed immersion. -/
@[stacks 063J] #check (@AlgebraicGeometry.IsKoszulRegularImmersion :
  ∀ {X Z : AlgebraicGeometry.Scheme.{u}}, (Z ⟶ X) → Prop)

#check (@AlgebraicGeometry.isKoszulRegularImmersion_iff :
  ∀ {X Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X),
    AlgebraicGeometry.IsKoszulRegularImmersion i ↔
      AlgebraicGeometry.IsImmersion i ∧
        ∃ U : X.Opens, ∃ j : Z ⟶ U.toScheme,
          AlgebraicGeometry.IsKoszulRegularClosedImmersion j ∧ j ≫ U.ι = i)

/- Definition 31.21.1 (3): an immersion is `H_1`-regular when it factors through an open
subscheme as an `H_1`-regular closed immersion. -/
@[stacks 063J] #check (@AlgebraicGeometry.IsH1RegularImmersion :
  ∀ {X Z : AlgebraicGeometry.Scheme.{u}}, (Z ⟶ X) → Prop)

#check (@AlgebraicGeometry.isH1RegularImmersion_iff :
  ∀ {X Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X),
    AlgebraicGeometry.IsH1RegularImmersion i ↔
      AlgebraicGeometry.IsImmersion i ∧
        ∃ U : X.Opens, ∃ j : Z ⟶ U.toScheme,
          AlgebraicGeometry.IsH1RegularClosedImmersion j ∧ j ≫ U.ι = i)

/- Definition 31.21.1 (4): an immersion is quasi-regular when it factors through an open
subscheme as a quasi-regular closed immersion. -/
@[stacks 063J] #check (@AlgebraicGeometry.IsQuasiRegularImmersion :
  ∀ {X Z : AlgebraicGeometry.Scheme.{u}}, (Z ⟶ X) → Prop)

#check (@AlgebraicGeometry.isQuasiRegularImmersion_iff :
  ∀ {X Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X),
    AlgebraicGeometry.IsQuasiRegularImmersion i ↔
      AlgebraicGeometry.IsImmersion i ∧
        ∃ U : X.Opens, ∃ j : Z ⟶ U.toScheme,
          AlgebraicGeometry.IsQuasiRegularClosedImmersion j ∧ j ≫ U.ι = i)
