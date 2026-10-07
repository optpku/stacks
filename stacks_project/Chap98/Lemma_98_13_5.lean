module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap98.«98_13_2_1_Smooth»
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change of smoothness on predeformations

Smoothness on associated predeformations is stable under 2-fibre-product
base change of 1-morphisms of categories fibred in groupoids over
`(Sch/S)_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- Lemma 98.13.5: if `S` is locally Noetherian and `f : X ⟶ Y`, `g : Z ⟶ Y`
are 1-morphisms of categories fibred in groupoids over `(Sch/S)_fppf`, and `f`
is smooth on predeformations, then so is the projection
`TwoFibreProduct.snd f g`. -/
@[stacks 07XV]
instance IsSmoothOnPredeformations.twoFibreProduct_snd
    {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [IsSmoothOnPredeformations f] :
    IsSmoothOnPredeformations (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
