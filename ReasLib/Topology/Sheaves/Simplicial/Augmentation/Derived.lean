/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.CategoryTheory.Adjunction.Derived.Bounded
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import ReasLib.Topology.Sheaves.Simplicial.Augmentation.Coefficients
public import ReasLib.Topology.Sheaves.Simplicial.Augmentation.Pushforward

/-!
# Bounded-below derived adjunction of a Zariski augmentation

An augmentation `a : Y ⟶ constSpace X` of simplicial spaces has abelian inverse
image `inverseImage a AddCommGrpCat.{u}`, left adjoint to
`directImage`/`augmentationPushforward`, together with the canonical `D⁺`
adjunction and unit `K ⟶ Ra_* a⁻¹ K`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.AbelianSheaf CategoryTheory.Functor CategoryTheory.Limits TopCat

noncomputable section

universe u

namespace CategoryTheory.SimplicialObject

variable {Y : SimplicialObject TopCat.{u}} {X : TopCat.{u}} (a : Y ⟶ constSpace X)

variable [HasSheafify (zariskiTopology Y) AddCommGrpCat.{u}]
variable [HasSheafify (zariskiTopology (constSpace X)) AddCommGrpCat.{u}]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

/-- The abelian direct image `a_*` of an augmentation agrees with `directImage`. -/
theorem augmentationPushforward_eq :
    augmentationPushforward a = directImage a AddCommGrpCat.{u} :=
  rfl

/-- Additivity of the abelian augmentation inverse image. -/
instance augmentationInverseImage_additive : ((inverseImage a AddCommGrpCat.{u})).Additive :=
  sorry

/-- The abelian augmentation inverse image preserves finite limits. -/
instance augmentationInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits ((inverseImage a AddCommGrpCat.{u})) :=
  sorry

/-- The abelian augmentation inverse image preserves finite colimits. -/
instance augmentationInverseImage_preservesFiniteColimits :
    PreservesFiniteColimits ((inverseImage a AddCommGrpCat.{u})) :=
  sorry

/-- The exact abelian inverse-image functor `a⁻¹` of an augmentation. -/
abbrev augmentationInverseImageExact :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ₑ
      Sheaf (zariskiTopology Y) AddCommGrpCat.{u} :=
  ExactFunctor.of ((inverseImage a AddCommGrpCat.{u}))

/-- The underlying functor of `augmentationInverseImageExact` is `a⁻¹`. -/
theorem augmentationInverseImageExact_obj :
    (augmentationInverseImageExact a).obj = (inverseImage a AddCommGrpCat.{u}) :=
  rfl

section Plus

variable [(augmentationPushforward a).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (zariskiTopology Y) AddCommGrpCat.{u}))]

/-- Bounded-below derived inverse image `a⁻¹` on `D⁺(X)`. -/
abbrev plusInverseImageDerived :
    DerivedCategory.Plus (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ⥤
      DerivedCategory.Plus (Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) :=
  Adjunction.Derived.Plus.left (augmentationInverseImageExact a)

/-- Bounded-below derived inverse image is the exact `D⁺` action of `a⁻¹`. -/
theorem plusInverseImageDerived_eq :
    plusInverseImageDerived a =
      Adjunction.Derived.Plus.left (augmentationInverseImageExact a) :=
  rfl

/-- Bounded-below total right-derived direct image `Ra_*` on `D⁺`. -/
abbrev plusDirectImageDerived :
    DerivedCategory.Plus (Sheaf (zariskiTopology Y) AddCommGrpCat.{u}) ⥤
      DerivedCategory.Plus (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  Adjunction.Derived.Plus.right (augmentationPushforward a)

/-- Bounded-below `Ra_*` is the canonical `D⁺` right-derived functor of `a_*`. -/
theorem plusDirectImageDerived_eq :
    plusDirectImageDerived a =
      Adjunction.Derived.Plus.right (augmentationPushforward a) :=
  rfl

/-- The bounded-below derived adjunction `a⁻¹ ⊣ Ra_*` on `D⁺`. -/
def plusDerivedAdjunction :
    plusInverseImageDerived a ⊣ plusDirectImageDerived a :=
  Adjunction.Derived.Plus.adjunction (augmentationInverseImageExact a)
    (augmentationPushforward a) (inverseImageAdjunction a AddCommGrpCat.{u})

/-- `plusDerivedAdjunction` is the exact-left bounded-below derived adjunction of
`inverseImageAdjunction`. -/
theorem plusDerivedAdjunction_eq :
    plusDerivedAdjunction a =
      Adjunction.Derived.Plus.adjunction (augmentationInverseImageExact a)
        (augmentationPushforward a) (inverseImageAdjunction a AddCommGrpCat.{u}) :=
  rfl

/-- The canonical `D⁺` derived unit `K ⟶ Ra_* a⁻¹ K`. -/
abbrev plusDerivedUnit :
    𝟭 (DerivedCategory.Plus (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})) ⟶
      plusInverseImageDerived a ⋙ plusDirectImageDerived a :=
  (plusDerivedAdjunction a).unit

/-- `plusDerivedUnit` is the unit of `plusDerivedAdjunction`. -/
theorem plusDerivedUnit_eq :
    plusDerivedUnit a = (plusDerivedAdjunction a).unit :=
  rfl

end Plus

end CategoryTheory.SimplicialObject

end
