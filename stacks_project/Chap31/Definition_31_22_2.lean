module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeRegularImmersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Definition 31.22.2 (1): an immersion `i : Z ⟶ X` over `f : X ⟶ S` is a relative
quasi-regular immersion if `Z ⟶ S` is flat and `i` is a quasi-regular immersion. -/
@[stacks 063S] #check
  (@AlgebraicGeometry.RelativeQuasiRegularImmersion :
    {X S Z : AlgebraicGeometry.Scheme.{u}} → (X ⟶ S) → (Z ⟶ X) → Prop)

#check
  (@AlgebraicGeometry.relativeQuasiRegularImmersion_iff :
    ∀ {X S Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X),
      AlgebraicGeometry.RelativeQuasiRegularImmersion f i ↔
        AlgebraicGeometry.IsQuasiRegularImmersion i ∧
          AlgebraicGeometry.Flat (i ≫ f))

/- Definition 31.22.2 (2): an immersion `i : Z ⟶ X` over `f : X ⟶ S` is a relative
`H_1`-regular immersion if `Z ⟶ S` is flat and `i` is an `H_1`-regular immersion. -/
@[stacks 063S] #check
  (@AlgebraicGeometry.RelativeH1RegularImmersion :
    {X S Z : AlgebraicGeometry.Scheme.{u}} → (X ⟶ S) → (Z ⟶ X) → Prop)

#check
  (@AlgebraicGeometry.relativeH1RegularImmersion_iff :
    ∀ {X S Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X),
      AlgebraicGeometry.RelativeH1RegularImmersion f i ↔
        AlgebraicGeometry.IsH1RegularImmersion i ∧
          AlgebraicGeometry.Flat (i ≫ f))
