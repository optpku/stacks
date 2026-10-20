module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line.Coproduct
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line.NonAffine
public import ReasLib.AlgebraicGeometry.Scheme.ProductSpectrum.Cardinality
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Exercise 111.53.4 (Examples) (1): the coproduct of two projective lines is reducible
and admits a closed immersion into projective three-space over the base field. -/
@[stacks 069U]
#check (AlgebraicGeometry.ProjectiveLine.Coprod.reducibleWithClosedImmersion :
  ∀ (k : Type u) [Field k],
    ¬ IrreducibleSpace (AlgebraicGeometry.ProjectiveLine.Coprod.scheme k) ∧
      ∃ immersion : AlgebraicGeometry.ProjectiveLine.Coprod.scheme k ⟶
          AlgebraicGeometry.ProjectiveSpace.scheme k 3,
        IsClosedImmersion immersion ∧
          immersion ≫ AlgebraicGeometry.ProjectiveSpace.toSpec k 3 =
            AlgebraicGeometry.ProjectiveLine.Coprod.toSpec k)

/- Exercise 111.53.4 (Examples) (2): the spectrum of a product of one hundred copies
of a field has exactly one hundred points. -/
@[stacks 069U]
#check (AlgebraicGeometry.Scheme.ProductSpectrum.card_fin 100 :
  ∀ (k : Type u) [Field k], Nat.card (Spec (.of (Fin 100 → k))) = 100)

/- Exercise 111.53.4 (Examples) (3): the structure morphism of the projective line is
not an affine morphism of schemes. -/
@[stacks 069U]
#check (AlgebraicGeometry.ProjectiveLine.not_isAffineHom_toSpec :
  ∀ (k : Type u) [Field k], ¬ IsAffineHom (AlgebraicGeometry.ProjectiveLine.toSpec k))
