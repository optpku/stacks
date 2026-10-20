module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Conormal.Transitivity
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# Conormal-differentials transitivity for formally unramified morphisms

For composable scheme morphisms `Z ⟶ X ⟶ Y`, formal unramifiedness of `Z ⟶ X` and
`Z ⟶ Y` makes the canonical conormal-differentials sequence exact through its terminal
zero.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.Conormal.Differentials.Transitivity

variable {Z X Y : Scheme.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology Z) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology Z) CommRingCat.{u}]
variable [(Opens.grothendieckTopology Z).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology Z).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Limits.HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u})]

/-- The conormal-differentials transitivity complex is exact when both `Z ⟶ X` and its
composite `Z ⟶ Y` are formally unramified. -/
theorem exact_of_formallyUnramified (i : Z ⟶ X) (f : X ⟶ Y)
    [FormallyUnramified i] [FormallyUnramified (i ≫ f)] :
    (complex i f).Exact := sorry

/-- The canonical map from `C_{Z/X}` to the pullback of `Ω_{X/Y}` is an epimorphism when
both `Z ⟶ X` and its composite `Z ⟶ Y` are formally unramified. -/
instance map_epi_of_formallyUnramified (i : Z ⟶ X) (f : X ⟶ Y)
    [FormallyUnramified i] [FormallyUnramified (i ≫ f)] :
    Epi (Conormal.Differentials.map i f) := sorry

/-- When `Z ⟶ X` and its composite `Z ⟶ Y` are formally unramified, the canonical
conormal-differentials transitivity complex is exact and its right arrow is an epimorphism. -/
theorem exact_and_epi_of_formallyUnramified (i : Z ⟶ X) (f : X ⟶ Y)
    [FormallyUnramified i] [FormallyUnramified (i ≫ f)] :
    (complex i f).Exact ∧ Epi (Conormal.Differentials.map i f) := sorry

end AlgebraicGeometry.Scheme.Hom.Conormal.Differentials.Transitivity
