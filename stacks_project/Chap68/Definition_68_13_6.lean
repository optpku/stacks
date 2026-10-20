module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidualSpace
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 68.13.6: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `x ∈ |X|`. The residual space of `X` at `x` is the monomorphism `Z_x ⟶ X`
constructed in Lemma 68.13.5. -/
@[stacks 06R0] #check (AlgebraicGeometry.AlgebraicSpace.IsResidualSpace :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S}, (Z ⟶ X) → Points X → Prop)
#check (AlgebraicGeometry.AlgebraicSpace.IsResidualSpace.exists_at :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Points X),
    ∃ (Z : AlgebraicSpace S) (ι : Z ⟶ X), IsResidualSpace ι x)
#check (AlgebraicGeometry.AlgebraicSpace.IsResidualSpace.existsUnique_iso :
  ∀ {S : Scheme.{u}} {X Z Z' : AlgebraicSpace S} {x : Points X}
    (ι : Z ⟶ X) (ι' : Z' ⟶ X) [IsResidualSpace ι x] [IsResidualSpace ι' x],
    ∃! e : Z ≅ Z', e.hom ≫ ι' = ι)
