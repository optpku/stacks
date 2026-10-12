/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Transitivity
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.UniversalFirstOrder.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.UniversalFirstOrder.ComparisonPullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.UniversalFirstOrder.Existence

/-!
# Conormal transitivity for formally unramified morphisms

The canonical conormal transitivity sequence of two composable formally unramified scheme
morphisms is exact through its terminal zero.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.Conormal.Transitivity

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

variable (i : Z ⟶ Y) (j : Y ⟶ X) [FormallyUnramified i] [FormallyUnramified j]

/-- The conormal transitivity short complex of two formally unramified scheme morphisms is
exact. -/
theorem exact_of_formallyUnramified : (complex i j).Exact := sorry

/-- The projection to `C_{Z/Y}` in the conormal transitivity sequence of formally
unramified scheme morphisms is an epimorphism. -/
instance projection_epi_of_formallyUnramified : Epi (projection i j) := sorry

/-- For formally unramified `Z ⟶ Y ⟶ X`, the canonical sequence
`i^* C_{Y/X} ⟶ C_{Z/X} ⟶ C_{Z/Y} ⟶ 0` is exact. -/
theorem exact_and_epi_of_formallyUnramified :
    (complex i j).Exact ∧ Epi (projection i j) := sorry

end AlgebraicGeometry.Scheme.Hom.Conormal.Transitivity
