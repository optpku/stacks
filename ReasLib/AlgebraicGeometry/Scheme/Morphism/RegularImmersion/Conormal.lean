module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Transitivity.Splitting
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion

/-!
# Regular immersions and locally split conormal transitivity

For an `H₁`-regular immersion followed by an immersion, the canonical conormal transitivity
sequence is short exact and locally split. Conversely, regularity of the first of two composable
immersions descends from the composite when this sequence is short exact and locally split. For
Koszul regularity, the second immersion is also assumed Koszul-regular.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {X Y Z : Scheme.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) CommRingCat.{u}]
variable [(Opens.grothendieckTopology ↥Z).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology ↥Z).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology ↥Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Limits.HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology ↥Z) CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Y) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Y) CommRingCat.{u}]
variable [(Opens.grothendieckTopology ↥Y).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology ↥Y).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology ↥Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Limits.HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology ↥Y) CommRingCat.{u})]

namespace IsQuasiRegularImmersion

/-- If the conormal transitivity complex is short exact and locally split, quasi-regularity of
the composite immersion descends to the first immersion. -/
theorem of_comp_of_split_conormal
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j]
    [LocallyOfFinitePresentation j]
    (hconormal : Scheme.Hom.Conormal.Transitivity.IsShortExactLocallySplit i j)
    [IsQuasiRegularImmersion (i ≫ j)] :
    IsQuasiRegularImmersion i := sorry

end IsQuasiRegularImmersion

namespace IsH1RegularImmersion

/-- The canonical conormal transitivity complex of an `H₁`-regular immersion followed by an
immersion is short exact and locally split. -/
theorem conormalTransitivity_isShortExactLocallySplit
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsH1RegularImmersion i] [IsImmersion j] :
    Scheme.Hom.Conormal.Transitivity.IsShortExactLocallySplit i j := sorry

/-- If the conormal transitivity complex is short exact and locally split, `H₁`-regularity of
the composite immersion descends to the first immersion. -/
theorem of_comp_of_split_conormal
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j]
    [LocallyOfFinitePresentation j]
    (hconormal : Scheme.Hom.Conormal.Transitivity.IsShortExactLocallySplit i j)
    [IsH1RegularImmersion (i ≫ j)] :
    IsH1RegularImmersion i := sorry

end IsH1RegularImmersion

namespace IsKoszulRegularImmersion

/-- If the conormal transitivity complex is short exact and locally split, Koszul-regularity of
the second and composite immersions implies Koszul-regularity of the first immersion. -/
theorem of_comp_of_split_conormal
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i]
    [LocallyOfFinitePresentation j] [IsKoszulRegularImmersion j]
    (hconormal : Scheme.Hom.Conormal.Transitivity.IsShortExactLocallySplit i j)
    [IsKoszulRegularImmersion (i ≫ j)] :
    IsKoszulRegularImmersion i := sorry

end IsKoszulRegularImmersion

end

end AlgebraicGeometry
