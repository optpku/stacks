module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap97.«97_6_0_1_Lifting»

/-!
# Base change of formally-smooth-on-objects 1-morphisms

Formal smoothness on objects for 1-morphisms of categories fibred in groupoids
over `(Sch/S)_fppf` is stable under 2-fibre-product base change.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

namespace AlgebraicGeometry.Groupoids.Hom.FormallySmoothOnObjects

/-- If `p : X ⟶ Y` is formally smooth on objects, then so is its base change
`TwoFibreProduct.fst q p : X ×_Y Z ⟶ Z` along any `q : Z ⟶ Y`. -/
instance pullback_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (p : X ⟶ Y) (q : Z ⟶ Y) [FormallySmoothOnObjects p] :
    FormallySmoothOnObjects (TwoFibreProduct.fst.{u + 1, u, u + 1, u} q p) :=
  sorry

end AlgebraicGeometry.Groupoids.Hom.FormallySmoothOnObjects
