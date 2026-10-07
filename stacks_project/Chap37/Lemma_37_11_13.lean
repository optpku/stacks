module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallySmooth.Differentials.Conormal
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.FormallySmooth

open Scheme.Hom.Conormal.Differentials.Transitivity

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
variable (i : Z ⟶ X) (f : X ⟶ Y) [FormallyUnramified i]
variable [FormallyUnramified (i ≫ f)] [FormallySmooth f]

/- Lemma 37.11.13: write the map `j : Z ⟶ Y` in the commutative triangle as the
composite `i ≫ f`. If `i` and `i ≫ f` are formally unramified and `f` is formally smooth,
then the canonical conormal-differentials transitivity complex is short exact and admits a
splitting after restriction to a source-open neighborhood of every point of `Z`. -/
@[stacks 067W] #check
  (AlgebraicGeometry.FormallySmooth.conormalDifferentialsTransitivity_shortExact_and_locallySplit
    i f :
    (complex i f).ShortExact ∧
      ∀ z : Z, ∃ U : Z.Opens, z ∈ U ∧
        Nonempty (((complex i f).map
          (Scheme.Modules.pullback U.ι)).Splitting))

end AlgebraicGeometry.FormallySmooth
