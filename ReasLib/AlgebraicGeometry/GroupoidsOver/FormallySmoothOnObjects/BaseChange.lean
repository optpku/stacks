module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormallySmoothOnObjects
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback

/-!
# Base change of formally smooth on objects morphisms

Formal smoothness on objects for morphisms of categories fibred in groupoids
over `(Sch/S)_fppf` is stable under two-fibre-product base change.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

namespace AlgebraicGeometry.Groupoids.Hom.FormallySmoothOnObjects

/-- If `p : X ⟶ Y` is formally smooth on objects, then the canonical projection
`TwoFibreProduct.fst q p` to `Z` is formally smooth on objects for every
`q : Z ⟶ Y`. -/
instance pullback_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (p : X ⟶ Y) (q : Z ⟶ Y) [FormallySmoothOnObjects p] :
    FormallySmoothOnObjects (TwoFibreProduct.fst.{u + 1, u, u + 1, u} q p) :=
  sorry

end AlgebraicGeometry.Groupoids.Hom.FormallySmoothOnObjects
