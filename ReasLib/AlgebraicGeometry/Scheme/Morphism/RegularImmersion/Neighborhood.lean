/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Conormal
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Regular immersions near a point

This file records regularity of a scheme morphism on a source-open neighborhood of a specified
point and relates this condition for two composable immersions to the conormal transitivity
complex.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes is a regular immersion near a source point if its restriction to some
source-open neighborhood of that point is a regular immersion. -/
def IsRegularImmersionNear {X Z : Scheme.{u}} (i : Z ⟶ X) (z : Z) : Prop :=
  ∃ U : Z.Opens, z ∈ U ∧ IsRegularImmersion (U.ι ≫ i)

/-- Regularity of a scheme morphism near a source point is characterized by a source-open
neighborhood on which its restriction is a regular immersion. -/
theorem isRegularImmersionNear_iff {X Z : Scheme.{u}} (i : Z ⟶ X) (z : Z) :
    IsRegularImmersionNear i z ↔
      ∃ U : Z.Opens, z ∈ U ∧ IsRegularImmersion (U.ι ≫ i) := sorry

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

/-- For two composable immersions into a locally Noetherian scheme, regularity of both factors,
regularity of the first factor and the composite, and regularity of the composite together with
a neighborhood splitting of the conormal transitivity complex are equivalent. -/
theorem isRegularImmersionNear_tfae_of_comp_and_conormal
    [IsLocallyNoetherian X] (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j]
    (z : Z) :
    List.TFAE
      [ IsRegularImmersionNear i z ∧ IsRegularImmersionNear j (i.base z),
        IsRegularImmersionNear i z ∧ IsRegularImmersionNear (i ≫ j) z,
        IsRegularImmersionNear (i ≫ j) z ∧
          Scheme.Hom.Conormal.Transitivity.IsSplitExactNear i j z ] := sorry

end

end AlgebraicGeometry
