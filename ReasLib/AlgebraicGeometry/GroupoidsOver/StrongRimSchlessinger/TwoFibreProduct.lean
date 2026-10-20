module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.StrongRimSchlessinger
public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic

/-!
# Two-fibre products and the strong Rim-Schlessinger condition

The strong Rim-Schlessinger condition is stable under canonical two-fibre products
of categories fibred in groupoids over a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- The canonical two-fibre product of a cospan of categories fibred in groupoids
over a scheme satisfies the strong Rim-Schlessinger condition when all three
categories satisfy it. -/
instance instHasStrongRimSchlessinger_twoFibreProduct
    {S : Scheme.{u}} {X Y Z : GroupoidsOver S} (p : X ⟶ Y) (q : Z ⟶ Y)
    [HasStrongRimSchlessinger X] [HasStrongRimSchlessinger Y]
    [HasStrongRimSchlessinger Z] :
    HasStrongRimSchlessinger (TwoFibreProduct.apex.{u + 1, u, u + 1, u} p q) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
