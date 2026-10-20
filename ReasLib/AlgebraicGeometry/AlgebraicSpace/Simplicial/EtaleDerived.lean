/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleAugmentation
public import ReasLib.CategoryTheory.Sites.Topos.Abelian
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.LeftExact
public import ReasLib.CategoryTheory.Adjunction.Derived.Bounded
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived

/-! # Bounded-below derived functors of total étale augmentation

The total étale augmentation induces an exact inverse image on abelian sheaves.
Its adjunction with abelian direct image yields a bounded-below derived adjunction.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Simplicial

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleDerived

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X)

/-- Abelian inverse image of the total étale augmentation preserves finite limits. -/
instance inverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (spacesEtaleAugmentation U a).abelianInverseImage :=
  sorry

/-- Abelian inverse image of the total étale augmentation preserves finite colimits. -/
instance inverseImage_preservesFiniteColimits :
    PreservesFiniteColimits (spacesEtaleAugmentation U a).abelianInverseImage :=
  sorry

/-- The exact abelian inverse image of the total étale augmentation. -/
def inverseImageExact :
    Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1} ⥤ₑ
      Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1} :=
  ExactFunctor.of (spacesEtaleAugmentation U a).abelianInverseImage

/-- The underlying exact functor is the abelian inverse image of total étale augmentation. -/
theorem inverseImageExact_obj :
    (inverseImageExact a).obj = (spacesEtaleAugmentation U a).abelianInverseImage := rfl

/-- Abelian direct image of the total étale augmentation is additive. -/
instance directImage_additive : (spacesEtaleAugmentation U a).abelianDirectImage.Additive :=
  sorry

/-- Abelian direct image of the total étale augmentation admits a bounded-below
right-derived functor. -/
instance directImage_hasRightDerivedFunctor :
    (spacesEtaleAugmentation U a).abelianDirectImage.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1})) :=
  sorry

/-- The bounded-below derived inverse image of total étale augmentation. -/
def plusInverseImage :
    DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}) :=
  Adjunction.Derived.Plus.left (inverseImageExact a)

/-- The bounded-below right-derived abelian direct image of total étale augmentation. -/
def plusDirectImage :
    DerivedCategory.Plus (Sheaf (spacesEtaleTotalTopology U) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) :=
  Adjunction.Derived.Plus.right (spacesEtaleAugmentation U a).abelianDirectImage

/-- The bounded-below derived adjunction of the total étale augmentation. -/
def plusAdjunction : plusInverseImage a ⊣ plusDirectImage a :=
  Adjunction.Derived.Plus.adjunction (inverseImageExact a)
    (spacesEtaleAugmentation U a).abelianDirectImage
    (spacesEtaleAugmentation U a).abelianAdjunction

/-- The canonical derived unit from a complex to the derived direct image of its
total étale augmentation inverse image. -/
def plusDerivedUnit :
    𝟭 (DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})) ⟶
      plusInverseImage a ⋙ plusDirectImage a :=
  (plusAdjunction a).unit

/-- The canonical derived unit is the unit of the derived total étale augmentation adjunction. -/
theorem plusDerivedUnit_eq : plusDerivedUnit a = (plusAdjunction a).unit := rfl

end AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleDerived
