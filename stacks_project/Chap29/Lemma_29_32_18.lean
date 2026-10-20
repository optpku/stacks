module

import ReasLib.AlgebraicGeometry.Scheme.Differentials.Conormal.Transitivity
import StacksCheckRecall

open CategoryTheory

noncomputable section

universe u

variable {Z X Y : AlgebraicGeometry.Scheme.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) CommRingCat.{u}]
variable [(Opens.grothendieckTopology ↥Z).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology ↥Z).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology ↥Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Limits.HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology ↥Z) CommRingCat.{u})]
variable (i : Z ⟶ X) (f : X ⟶ Y) [AlgebraicGeometry.IsImmersion i]
variable [AlgebraicGeometry.IsImmersion (i ≫ f)]

/- Lemma 29.32.18: For immersions `Z ⟶ X` and `Z ⟶ Y`, the canonical sequence from
`C_{Z/Y}` through `C_{Z/X}` to the pullback of `Ω_{X/Y}` is exact and ends in zero. -/
@[stacks 067L] #check
  (AlgebraicGeometry.Scheme.Hom.Conormal.Differentials.Transitivity.exact_and_epi i f :
    (AlgebraicGeometry.Scheme.Hom.Conormal.Differentials.Transitivity.complex i f).Exact ∧
      Epi (AlgebraicGeometry.Scheme.Hom.Conormal.Differentials.map i f))
