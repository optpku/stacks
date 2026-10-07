module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Conormal.Transitivity
import Mathlib.Tactic.CrossRefAttribute

/-!
# Conormal Differentials for Smooth Scheme Morphisms

For an immersion `Z ⟶ X` over a scheme `S`, smoothness of `Z ⟶ S` makes the canonical
conormal complex of relative differentials short exact.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

variable {Z X Y S : Scheme.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) CommRingCat.{u}]
variable [(Opens.grothendieckTopology ↥Z).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology ↥Z).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology ↥Z) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology ↥Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Limits.HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology ↥Z) CommRingCat.{u})]

/-- If an immersed scheme `Z` is smooth over `S`, then its canonical conormal complex

`C_{Z/X} ⟶ i^* Ω_{X/S} ⟶ Ω_{Z/S}`

is short exact. -/
@[stacks 06AA]
theorem Smooth.conormalDifferentials_shortExact
    (i : Z ⟶ X) [IsImmersion i] (f : X ⟶ S) [Smooth (i ≫ f)] :
    (Scheme.Hom.Conormal.Differentials.complex i f).ShortExact := sorry

/-- If `Z ⟶ X` and `Z ⟶ Y` are immersions and `X ⟶ Y` is smooth, then the canonical
conormal-differentials transitivity complex

`C_{Z/Y} ⟶ C_{Z/X} ⟶ i^* Ω_{X/Y}`

is short exact. -/
@[stacks 06AB]
theorem Smooth.conormalDifferentialsTransitivity_shortExact
    (i : Z ⟶ X) (f : X ⟶ Y) [IsImmersion i] [IsImmersion (i ≫ f)] [Smooth f] :
    (Scheme.Hom.Conormal.Differentials.Transitivity.complex i f).ShortExact := sorry

end AlgebraicGeometry
