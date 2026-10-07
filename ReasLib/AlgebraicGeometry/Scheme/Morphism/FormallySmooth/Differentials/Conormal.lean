module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Conormal.Transitivity.FormallyUnramified
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.UniversalFirstOrder.ConormalSequence
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallySmooth
import Mathlib.Tactic.CrossRefAttribute

/-!
# Conormal differentials for formally smooth scheme morphisms

Formal smoothness over a base makes canonical conormal-differentials complexes short exact.
For a composable formally unramified pair, the transitivity complex is also locally split.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FormallySmooth

open Thickening Thickening.IsUniversalFirstOrder
open Scheme.Hom.Conormal.Differentials.Transitivity

/-- If a formally unramified morphism represented by a universal first-order thickening is
formally smooth over the base, then its canonical conormal-differentials complex is short
exact. -/
@[stacks 06B7]
theorem conormalDifferentials_shortExact
    {X S : Scheme.{u}} (T : Thickening.Over X) (f : X ⟶ S)
    [FormallyUnramified T.left.hom] [IsUniversalFirstOrder T]
    [FormallySmooth (T.left.hom ≫ f)] :
    (Differentials.complex T f).ShortExact := sorry

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

/-- If `Z ⟶ X` and its composite `Z ⟶ Y` are formally unramified and `X ⟶ Y` is
formally smooth, then the conormal-differentials transitivity complex is short exact and
is split after restriction to a source-open neighborhood of every point of `Z`. -/
@[stacks 067W]
theorem conormalDifferentialsTransitivity_shortExact_and_locallySplit
    (i : Z ⟶ X) (f : X ⟶ Y) [FormallyUnramified i]
    [FormallyUnramified (i ≫ f)] [FormallySmooth f] :
    (complex i f).ShortExact ∧
      ∀ z : Z, ∃ U : Z.Opens, z ∈ U ∧
        Nonempty (((complex i f).map
          (Scheme.Modules.pullback U.ι)).Splitting) := sorry

end AlgebraicGeometry.FormallySmooth
