module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Approximation
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback

/-!
# Approximation of two-fibre products of categories fibred in groupoids

Equivalence of the complete-local-to-formal approximation functor is preserved
under two-fibre products.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- If the canonical approximation functors for `X`, `Y`, and `Z` are equivalences,
then the approximation functor for the two-fibre product of any morphisms
`p : X ⟶ Y` and `q : Z ⟶ Y` is an equivalence. -/
@[stacks 07X9]
instance approximation_twoFibreProduct {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X Y Z : GroupoidsOver S} (p : X ⟶ Y) (q : Z ⟶ Y)
    [(approximation X).IsEquivalence] [(approximation Y).IsEquivalence]
    [(approximation Z).IsEquivalence] :
    (approximation (TwoFibreProduct.apex.{u + 1, u, u + 1, u} p q)).IsEquivalence :=
  sorry

end AlgebraicGeometry.GroupoidsOver
