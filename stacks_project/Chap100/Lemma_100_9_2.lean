module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Immersion
import StacksCheckRecall

/-!
# Base change of immersions of algebraic stacks

Immersions, closed immersions, and open immersions of algebraic stacks are
stable under arbitrary two-fibre-product base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/- Lemma 100.9.2. Base change of an immersion of algebraic stacks is an
immersion; the same holds for closed and open immersions. -/
@[stacks 0501] #check (AlgebraicGeometry.Groupoids.Hom.Immersion.twoFibreProduct_snd :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (i : Z ⟶ Y) [Immersion i],
    Immersion (TwoFibreProduct.snd.{u + 1, u, u + 1, u} i f))

/- Lemma 100.9.2, closed immersion case. -/
@[stacks 0501] #check (AlgebraicGeometry.Groupoids.Hom.ClosedImmersion.twoFibreProduct_snd :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (i : Z ⟶ Y) [ClosedImmersion i],
    ClosedImmersion (TwoFibreProduct.snd.{u + 1, u, u + 1, u} i f))

/- Lemma 100.9.2, open immersion case. -/
@[stacks 0501] #check (AlgebraicGeometry.Groupoids.Hom.OpenImmersion.twoFibreProduct_snd :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (i : Z ⟶ Y) [OpenImmersion i],
    OpenImmersion (TwoFibreProduct.snd.{u + 1, u, u + 1, u} i f))

end AlgebraicGeometry.Groupoids.Hom
