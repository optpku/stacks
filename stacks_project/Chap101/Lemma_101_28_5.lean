module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap101.Definition_101_28_1_Gerbe
public import stacks_project.Chap101.Lemma_101_25_5_Surjective
public import stacks_project.Chap101.Lemma_101_25_5_Flat
public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation

/-!
# Descent of gerbes of algebraic stacks along fppf morphisms

In a fibre product square of algebraic stacks, if the changed-base morphism
is surjective, flat, and locally of finite presentation, then being a gerbe
over the changed base implies being a gerbe over the original base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Gerbe

/-- Lemma 101.28.5: let `f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms of algebraic
stacks, and let `c` be a fibre-product cone. If `g` is surjective, flat, and
locally of finite presentation and `c.snd` makes the apex a gerbe over `Z`,
then `X` is a gerbe over `Y`. -/
@[stacks 06QF]
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y}
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] [c.IsBilimit]
    [Gerbe c.snd] :
    Gerbe f :=
  sorry

/-- Being a gerbe over the target of a morphism of algebraic stacks follows
from being a gerbe over the second projection of a chosen 2-fibre product
against a surjective, flat, locally of finite presentation morphism. -/
theorem of_twoFibreProduct_snd {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] (f : X ⟶ Y) (g : Z ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)]
    [Gerbe (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)] :
    Gerbe f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Gerbe
