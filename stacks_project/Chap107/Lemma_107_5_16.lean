module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.PseudoCatenary.FiniteType
import StacksCheckRecall

/-!
# Pseudo-catenary algebraic stacks along locally of finite type morphisms

A morphism of algebraic stacks that is locally of finite type into a
pseudo-catenary locally Noetherian target has pseudo-catenary source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 107.5.16: if `X` is a pseudo-catenary locally Noetherian algebraic
stack and `f : Y ⟶ X` is locally of finite type, then there exists a smooth
surjective morphism `V ⟶ Y` whose source is a universally catenary scheme,
hence `Y` is pseudo-catenary. Local Noetherianity of `X` follows from its
pseudo-catenary hypothesis. -/
@[stacks 0DRW] #check
  (AlgebraicGeometry.AlgebraicStack.IsPseudoCatenary.of_locallyOfFiniteType :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [IsPseudoCatenary X]
      (f : Y ⟶ X) [LocallyOfFiniteType f], IsPseudoCatenary Y)

end AlgebraicGeometry.AlgebraicStack
