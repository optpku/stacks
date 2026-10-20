module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe.Descent
import StacksCheckRecall

/-!
# Descent of gerbes of algebraic stacks along fppf morphisms

For `f : X ⟶ Y` and a surjective, flat, locally of finite presentation
base-change morphism `g : Z ⟶ Y`, being a gerbe after base change along `g`
implies that `f` is a gerbe over `Y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Gerbe

/- Lemma 101.28.5: let `f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms of algebraic
stacks, and let `c` be a fibre-product cone. If `g` is surjective, flat, and
locally of finite presentation and `c.snd` makes the apex a gerbe over `Z`,
then `X` is a gerbe over `Y`. -/
@[stacks 06QF] #check (AlgebraicGeometry.AlgebraicStack.Gerbe.of_isBilimit :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y}
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] [c.IsBilimit]
    [Gerbe c.snd],
    Gerbe f)

/- Being a gerbe over the target of a morphism of algebraic stacks follows
from being a gerbe over the second projection of a chosen 2-fibre product
against a surjective, flat, locally of finite presentation morphism. -/
#check (AlgebraicGeometry.AlgebraicStack.Gerbe.of_twoFibreProduct_snd :
    ∀ {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] (f : X ⟶ Y) (g : Z ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)]
    [Gerbe (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)],
    Gerbe f)

end AlgebraicGeometry.AlgebraicStack.Gerbe
