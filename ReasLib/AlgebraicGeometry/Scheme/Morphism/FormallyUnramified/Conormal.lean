module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Transitivity.FormallyUnramified
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Koszul

/-!
# Conormal transitivity for formally unramified morphisms

The conormal transitivity complex is short exact when its morphisms are formally unramified
and the first morphism is locally of complete-intersection type.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormallyUnramified

open Scheme.Hom.Conormal.Transitivity

variable {X Y Z : Scheme.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology Z) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology Z) CommRingCat.{u}]
variable [(Opens.grothendieckTopology Z).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology Z).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology Z).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology Y) (Type u)]
variable [HasWeakSheafify (Opens.grothendieckTopology Y) CommRingCat.{u}]
variable [(Opens.grothendieckTopology Y).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [(Opens.grothendieckTopology Y).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasBinaryCoproducts
  (CategoryTheory.Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u})]

/-- For composable formally unramified scheme morphisms, the conormal transitivity complex is
short exact when the first morphism is locally of complete-intersection type. -/
theorem conormalTransitivity_shortExact_of_localCompleteIntersection
    (i : Z ⟶ Y) (j : Y ⟶ X) [FormallyUnramified i] [FormallyUnramified j]
    [LocallyOfType RingHom.IsLocalCompleteIntersection i] :
    (complex i j).ShortExact := sorry

end AlgebraicGeometry.FormallyUnramified
