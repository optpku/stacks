module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.LimitPreserving
public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic

/-!
# Fibre products of limit-preserving categories fibred in groupoids

Limit preservation on objects and full limit preservation are stable under
2-fibre products of categories fibred in groupoids over `(Sch/S)_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids
open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects

/-- If the structure morphisms of `X` and `Z` are limit preserving on objects
and `Y` is limit preserving, then the structure morphism of the two-fibre
product `X ×_Y Z` is limit preserving on objects. -/
instance twoFibreProduct {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (p : X ⟶ Y) (q : Z ⟶ Y)
    [LimitPreservingOnObjects (baseProjection.{u + 1, u, u + 1} X)]
    [LimitPreserving Y]
    [LimitPreservingOnObjects (baseProjection.{u + 1, u, u + 1} Z)] :
    LimitPreservingOnObjects
      (baseProjection.{u + 1, u, u + 1}
        (TwoFibreProduct.apex.{u + 1, u, u + 1, u} p q)) :=
  sorry

end AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects

namespace AlgebraicGeometry.Groupoids.LimitPreserving

/-- The two-fibre product of limit-preserving categories fibred in groupoids
over a limit-preserving category fibred in groupoids is limit preserving. -/
instance twoFibreProduct {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (p : X ⟶ Y) (q : Z ⟶ Y)
    [LimitPreserving X] [LimitPreserving Y] [LimitPreserving Z] :
    LimitPreserving (TwoFibreProduct.apex.{u + 1, u, u + 1, u} p q) :=
  sorry

end AlgebraicGeometry.Groupoids.LimitPreserving
