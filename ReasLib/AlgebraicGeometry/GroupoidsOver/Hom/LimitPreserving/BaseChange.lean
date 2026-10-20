module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Hom.LimitPreserving
public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic

/-!
# Base change of limit-preserving 1-morphisms

Limit preservation for 1-morphisms of categories fibred in groupoids over
`(Sch/S)_fppf` is stable under arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom.LimitPreserving

/-- The base change of a limit-preserving 1-morphism of categories fibred in
groupoids along any 1-morphism is limit preserving. -/
instance pullback_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (p : X ⟶ Y) (q : Z ⟶ Y) [LimitPreserving p] :
    LimitPreserving (TwoFibreProduct.snd.{u + 1, u, u + 1, u} p q) := sorry

end AlgebraicGeometry.Groupoids.Hom.LimitPreserving
