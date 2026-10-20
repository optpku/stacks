module

public import ReasLib.RingTheory.DualNumberPair
public import ReasLib.RingTheory.DualNumber.Scale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.DottedArrowOperations
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped DualNumber DualNumberPair

universe u

/- Exercise 111.35.5 -/
@[stacks 029H] #check (AlgebraicGeometry.Scheme.Hom.tangentAdd :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S} {x : X},
    AlgebraicGeometry.Scheme.Hom.DottedTangentArrow f x →
      AlgebraicGeometry.Scheme.Hom.DottedTangentArrow f x →
        AlgebraicGeometry.Scheme.Hom.DottedTangentArrow f x)

/- Exercise 111.35.5 -/
@[stacks 029H] #check (AlgebraicGeometry.Scheme.Hom.tangentSmul :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S} {x : X},
    X.residueField x →
      AlgebraicGeometry.Scheme.Hom.DottedTangentArrow f x →
        AlgebraicGeometry.Scheme.Hom.DottedTangentArrow f x)

/- Exercise 111.35.5 -/
@[stacks 029H] #check (AlgebraicGeometry.Scheme.Hom.tangentAdd_eq_add :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S} {x : X}
    (θ₁ θ₂ : AlgebraicGeometry.Scheme.Hom.DottedTangentArrow f x),
    AlgebraicGeometry.Scheme.Hom.tangentAdd θ₁ θ₂ = θ₁ + θ₂)

/- Exercise 111.35.5 -/
@[stacks 029H] #check (AlgebraicGeometry.Scheme.Hom.tangentSmul_eq_smul :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S} {x : X}
    (c : X.residueField x)
    (θ : AlgebraicGeometry.Scheme.Hom.DottedTangentArrow f x),
    AlgebraicGeometry.Scheme.Hom.tangentSmul c θ = c • θ)
