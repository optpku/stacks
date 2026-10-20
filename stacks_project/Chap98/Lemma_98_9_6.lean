module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.TwoFibreProduct
import StacksCheckRecall

/-!
# Approximation of 2-fibre products of categories fibred in groupoids

If the approximation functor from complete local objects to formal objects is an
equivalence for `X`, `Y`, and `Z`, then it is an equivalence for the 2-fibre
product `X ×_Y Z`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.GroupoidsOver

/- Lemma 98.9.6: if `S` is a scheme and `p : X ⟶ Y`, `q : Z ⟶ Y` are 1-morphisms
of categories fibred in groupoids over `(Sch/S)_fppf`, and the approximation
functor is an equivalence for `X`, `Y`, and `Z`, then it is an equivalence for
the 2-fibre product `X ×_Y Z`. -/
@[stacks 07X9]
#check (AlgebraicGeometry.GroupoidsOver.approximation_twoFibreProduct :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X Y Z : GroupoidsOver S} (p : X ⟶ Y) (q : Z ⟶ Y)
    [(approximation X).IsEquivalence] [(approximation Y).IsEquivalence]
    [(approximation Z).IsEquivalence],
    (approximation (TwoFibreProduct.apex.{u + 1, u, u + 1, u} p q)).IsEquivalence)

end AlgebraicGeometry.GroupoidsOver
