/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Differentials.Conormal

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

variable {Z X Y : Scheme.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) CommRingCat.{u}]
variable [(Opens.grothendieckTopology ↥Z).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology ↥Z).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology ↥Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Limits.HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology ↥Z) CommRingCat.{u})]
variable (i : Z ⟶ X) (f : X ⟶ Y) [IsImmersion i] [IsImmersion (i ≫ f)] [Smooth f]

/- Lemma 29.34.18: Normalize the commutative triangle by writing its morphism `Z ⟶ Y`
as `i ≫ f`. If `i` and `i ≫ f` are immersions and `f` is smooth, then the canonical
conormal-differentials transitivity complex is short exact. -/
@[stacks 06AB] #check
  (AlgebraicGeometry.Smooth.conormalDifferentialsTransitivity_shortExact i f :
    (Scheme.Hom.Conormal.Differentials.Transitivity.complex i f).ShortExact)

end AlgebraicGeometry
