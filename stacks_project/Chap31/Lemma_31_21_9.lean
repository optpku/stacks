module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Neighborhood

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Both morphisms in a composable pair are regular immersions near a specified source point
and its image. -/
abbrev regularImmersionNearFactors {X Y Z : Scheme.{u}}
    (i : Z ⟶ Y) (j : Y ⟶ X) (z : Z) : Prop :=
  IsRegularImmersionNear i z ∧ IsRegularImmersionNear j (i.base z)

end AlgebraicGeometry

/- Lemma 31.21.9: let `i : Z ⟶ Y` and `j : Y ⟶ X` be immersions of schemes, let `z : Z`,
and let the corresponding points of `Y` and `X` be their images. If `X` is locally Noetherian,
then the following are equivalent: both factors are regular immersions near the relevant points;
the first factor and the composite are regular immersions near `z`; and the composite is a
regular immersion near `z` while the canonical conormal transitivity complex is split exact on
a neighborhood of `z`. -/
@[stacks 0690] #check
  (AlgebraicGeometry.isRegularImmersionNear_tfae_of_comp_and_conormal :
    ∀ {X Y Z : Scheme.{u}}
      [HasWeakSheafify (Opens.grothendieckTopology ↥Z) (Type u)]
      [HasWeakSheafify (Opens.grothendieckTopology ↥Z) CommRingCat.{u}]
      [(Opens.grothendieckTopology ↥Z).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
      [(Opens.grothendieckTopology ↥Z).HasSheafCompose
        (CategoryTheory.forget CommRingCat.{u})]
      [HasWeakSheafify (Opens.grothendieckTopology ↥Z) AddCommGrpCat.{u}]
      [(Opens.grothendieckTopology ↥Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
      [Limits.HasBinaryCoproducts
        (CategoryTheory.Sheaf (Opens.grothendieckTopology ↥Z) CommRingCat.{u})]
      [HasWeakSheafify (Opens.grothendieckTopology ↥Y) (Type u)]
      [HasWeakSheafify (Opens.grothendieckTopology ↥Y) CommRingCat.{u}]
      [(Opens.grothendieckTopology ↥Y).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
      [(Opens.grothendieckTopology ↥Y).HasSheafCompose
        (CategoryTheory.forget CommRingCat.{u})]
      [HasWeakSheafify (Opens.grothendieckTopology ↥Y) AddCommGrpCat.{u}]
      [(Opens.grothendieckTopology ↥Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
      [Limits.HasBinaryCoproducts
        (CategoryTheory.Sheaf (Opens.grothendieckTopology ↥Y) CommRingCat.{u})]
      [IsLocallyNoetherian X]
      (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] (z : Z),
      List.TFAE
        [ IsRegularImmersionNear i z ∧ IsRegularImmersionNear j (i.base z),
          IsRegularImmersionNear i z ∧ IsRegularImmersionNear (i ≫ j) z,
          IsRegularImmersionNear (i ≫ j) z ∧
            Scheme.Hom.Conormal.Transitivity.IsSplitExactNear i j z ])
