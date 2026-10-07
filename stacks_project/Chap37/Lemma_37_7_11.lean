module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Conormal.Transitivity.FormallyUnramified
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace Conormal.Differentials.Transitivity

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

variable (i : Z ⟶ X) (f : X ⟶ Y)
variable [FormallyUnramified i] [FormallyUnramified (i ≫ f)]

/- Lemma 37.7.11: if `i` and `i ≫ f` are formally unramified, then the canonical
sequence `C_{Z/Y} ⟶ C_{Z/X} ⟶ i^* Ω_{X/Y} ⟶ 0` is exact. -/
@[stacks 067V] #check
  (AlgebraicGeometry.Scheme.Hom.Conormal.Differentials.Transitivity.exact_and_epi_of_formallyUnramified
    i f :
      (complex i f).Exact ∧ Epi (Conormal.Differentials.map i f))

end Conormal.Differentials.Transitivity
end AlgebraicGeometry.Scheme.Hom
