module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Conormal
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
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

/- Lemma 31.21.8 (1): if the canonical conormal sequence for immersions `i : Z ⟶ Y` and
`j : Y ⟶ X` is short exact and locally split, and `j` is locally of finite presentation, then
quasi-regularity of `i ≫ j` implies quasi-regularity of `i`. -/
@[stacks 068Z] #check
  (AlgebraicGeometry.IsQuasiRegularImmersion.of_comp_of_split_conormal :
    ∀ (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j]
      [LocallyOfFinitePresentation j]
      (_ : Scheme.Hom.Conormal.Transitivity.IsShortExactLocallySplit i j)
      [IsQuasiRegularImmersion (i ≫ j)],
      IsQuasiRegularImmersion i)

/- Lemma 31.21.8 (2): if the canonical conormal sequence for immersions `i : Z ⟶ Y` and
`j : Y ⟶ X` is short exact and locally split, and `j` is locally of finite presentation, then
`H₁`-regularity of `i ≫ j` implies `H₁`-regularity of `i`. -/
@[stacks 068Z] #check
  (AlgebraicGeometry.IsH1RegularImmersion.of_comp_of_split_conormal :
    ∀ (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j]
      [LocallyOfFinitePresentation j]
      (_ : Scheme.Hom.Conormal.Transitivity.IsShortExactLocallySplit i j)
      [IsH1RegularImmersion (i ≫ j)],
      IsH1RegularImmersion i)

/- Lemma 31.21.8 (3): if the canonical conormal sequence for immersions `i : Z ⟶ Y` and
`j : Y ⟶ X` is short exact and locally split, `j` is locally of finite presentation, and both
`j` and `i ≫ j` are Koszul-regular, then `i` is Koszul-regular. -/
@[stacks 068Z] #check
  (AlgebraicGeometry.IsKoszulRegularImmersion.of_comp_of_split_conormal :
    ∀ (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i]
      [LocallyOfFinitePresentation j] [IsKoszulRegularImmersion j]
      (_ : Scheme.Hom.Conormal.Transitivity.IsShortExactLocallySplit i j)
      [IsKoszulRegularImmersion (i ≫ j)],
      IsKoszulRegularImmersion i)

end

end AlgebraicGeometry
