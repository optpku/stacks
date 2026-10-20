module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidualSpace

/-!
# Residual spaces of algebraic spaces

A residual space of an algebraic space `X` at a point `x` is a monomorphism
`Z ⟶ X` from a reduced, locally Noetherian singleton algebraic space whose
image on points is `{x}`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.IsResidualSpace :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S}, (Z ⟶ X) → Points X → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.IsResidualSpace.spec :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} {ι : Z ⟶ X}
    {x : Points X} [IsResidualSpace ι x],
    Mono ι ∧ IsReduced Z ∧ IsLocallyNoetherian Z ∧ Subsingleton (Points Z) ∧
      Set.range (Points.map ι) = {x})

#check (AlgebraicGeometry.AlgebraicSpace.IsResidualSpace.iff :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (ι : Z ⟶ X) (x : Points X),
    IsResidualSpace ι x ↔
      Mono ι ∧ IsReduced Z ∧ IsLocallyNoetherian Z ∧ Subsingleton (Points Z) ∧
        Set.range (Points.map ι) = {x})

#check (AlgebraicGeometry.AlgebraicSpace.IsResidualSpace.id :
  ∀ {S : Scheme.{u}} {Z : AlgebraicSpace S} [IsReduced Z]
    [IsLocallyNoetherian Z] [Subsingleton (Points Z)] {x : Points Z},
    IsResidualSpace (𝟙 Z) x)

#check (AlgebraicGeometry.AlgebraicSpace.IsResidualSpace.map_eq :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} {ι : Z ⟶ X}
    {x : Points X} [IsResidualSpace ι x] (z : Points Z), Points.map ι z = x)
