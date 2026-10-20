/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Category.LCCat.Simplicial
public import ReasLib.Topology.Category.LCCat.ProperHypercovering
public import ReasLib.Topology.Sheaves.Simplicial.Cartesian

/-!
# Sheaf descent along proper hypercoverings

Augmentation inverse image identifies sheaves of sets and abelian sheaves on the
target of a proper hypercovering with cartesian sheaves on its simplicial Zariski
site. The quasi-inverse is the corresponding augmentation direct image.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor CategoryTheory.SimplicialObject
open scoped Simplicial MorphismOfTopoiIn

noncomputable section

namespace LCCat

variable {U : SimplicialObject LCCat.{u}} {X : LCCat.{u}}
variable (a : U ⟶ (SimplicialObject.const LCCat.{u}).obj X)

/-- Augmentation inverse image on sheaves of sets, corestricted to cartesian sheaves. -/
def sheafCartesianFunctor :
    Sheaf (Opens.grothendieckTopology X.obj) (Type u) ⥤
      Cartesian (forgetToTop.obj U) (Type u) :=
  (cartesianProperty (forgetToTop.obj U) (Type u)).lift
    (LeftExactAdjunction.inverseImage (augmentationMorphism (toTopCatAugmentation a)))
    fun F ↦ augmentationMorphism_inverseImage_isCartesian (toTopCatAugmentation a) F

/-- The underlying object of cartesian inverse image is geometric inverse image. -/
theorem sheafCartesianFunctor_obj
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type u)) :
    ((sheafCartesianFunctor a).obj F).obj =
      (LeftExactAdjunction.inverseImage
        (augmentationMorphism (toTopCatAugmentation a))).obj F :=
  rfl

/-- Augmentation direct image restricted to cartesian sheaves of sets. -/
def sheafCartesianInverse :
    Cartesian (forgetToTop.obj U) (Type u) ⥤
      Sheaf (Opens.grothendieckTopology X.obj) (Type u) :=
  (cartesianProperty (forgetToTop.obj U) (Type u)).ι ⋙
    (augmentationMorphism (toTopCatAugmentation a)).pushforward

/-- Cartesian direct image applies geometric pushforward to the underlying sheaf. -/
theorem sheafCartesianInverse_obj (G : Cartesian (forgetToTop.obj U) (Type u)) :
    (sheafCartesianInverse a).obj G =
      (augmentationMorphism (toTopCatAugmentation a)).pushforward.obj G.obj :=
  rfl

/-- The geometric augmentation adjunction unit is an isomorphism along a proper hypercovering. -/
theorem sheaf_unit_app_isIso (ha : IsProperHypercovering a)
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type u)) :
    IsIso ((augmentationMorphism (toTopCatAugmentation a)).adjunction.unit.app F) :=
  sorry

/-- The geometric augmentation adjunction counit is an isomorphism on cartesian sheaves
of sets along a proper hypercovering. -/
theorem sheaf_counit_app_isIso_of_isCartesian (ha : IsProperHypercovering a)
    (G : Sheaf (zariskiTopology (forgetToTop.obj U)) (Type u))
    (h : IsCartesian (forgetToTop.obj U) (Type u) G) :
    IsIso ((augmentationMorphism (toTopCatAugmentation a)).adjunction.counit.app G) :=
  sorry

/-- Naturality of the unit components of set-valued proper-hypercovering descent. -/
theorem sheafCartesianUnitIso_naturality (ha : IsProperHypercovering a)
    {F G : Sheaf (Opens.grothendieckTopology X.obj) (Type u)} (f : F ⟶ G) :
    (𝟭 (Sheaf (Opens.grothendieckTopology X.obj) (Type u))).map f ≫
        (@asIso _ _ _ _
          ((augmentationMorphism (toTopCatAugmentation a)).adjunction.unit.app G)
          (sheaf_unit_app_isIso a ha G)).hom =
      (@asIso _ _ _ _
          ((augmentationMorphism (toTopCatAugmentation a)).adjunction.unit.app F)
          (sheaf_unit_app_isIso a ha F)).hom ≫
        (sheafCartesianFunctor a ⋙ sheafCartesianInverse a).map f :=
  sorry

/-- The unit isomorphism `𝟭 ≅ a⁻¹ ⋙ a_*` of set-valued proper hypercovering descent. -/
def sheafCartesianUnitIso (ha : IsProperHypercovering a) :
    𝟭 (Sheaf (Opens.grothendieckTopology X.obj) (Type u)) ≅
      sheafCartesianFunctor a ⋙ sheafCartesianInverse a :=
  NatIso.ofComponents
    (fun F ↦
      @asIso _ _ _ _
        ((augmentationMorphism (toTopCatAugmentation a)).adjunction.unit.app F)
        (sheaf_unit_app_isIso a ha F))
    (fun f ↦ sheafCartesianUnitIso_naturality a ha f)

/-- Naturality of the counit components of set-valued proper-hypercovering descent. -/
theorem sheafCartesianCounitIso_naturality (ha : IsProperHypercovering a)
    {F G : Cartesian (forgetToTop.obj U) (Type u)} (f : F ⟶ G) :
    (sheafCartesianInverse a ⋙ sheafCartesianFunctor a).map f ≫
        ((cartesianProperty (forgetToTop.obj U) (Type u)).isoMk
          (@asIso _ _ _ _
            ((augmentationMorphism (toTopCatAugmentation a)).adjunction.counit.app G.obj)
            (sheaf_counit_app_isIso_of_isCartesian a ha G.obj G.property))).hom =
      ((cartesianProperty (forgetToTop.obj U) (Type u)).isoMk
          (@asIso _ _ _ _
            ((augmentationMorphism (toTopCatAugmentation a)).adjunction.counit.app F.obj)
            (sheaf_counit_app_isIso_of_isCartesian a ha F.obj F.property))).hom ≫
        (𝟭 (Cartesian (forgetToTop.obj U) (Type u))).map f :=
  sorry

/-- The counit isomorphism `a_* ⋙ a⁻¹ ≅ 𝟭` on cartesian sheaves of sets. -/
def sheafCartesianCounitIso (ha : IsProperHypercovering a) :
    sheafCartesianInverse a ⋙ sheafCartesianFunctor a ≅
      𝟭 (Cartesian (forgetToTop.obj U) (Type u)) :=
  NatIso.ofComponents
    (fun G ↦
      (cartesianProperty (forgetToTop.obj U) (Type u)).isoMk
        (@asIso _ _ _ _
          ((augmentationMorphism (toTopCatAugmentation a)).adjunction.counit.app G.obj)
          (sheaf_counit_app_isIso_of_isCartesian a ha G.obj G.property)))
    (fun f ↦ sheafCartesianCounitIso_naturality a ha f)

/-- A proper hypercovering identifies sheaves of sets on its target with cartesian
sheaves on its simplicial Zariski site, via augmentation inverse and direct image. -/
def sheafCartesianEquivalence (ha : IsProperHypercovering a) :
    Sheaf (Opens.grothendieckTopology X.obj) (Type u) ≌
      Cartesian (forgetToTop.obj U) (Type u) :=
  CategoryTheory.Equivalence.mk (sheafCartesianFunctor a) (sheafCartesianInverse a)
    (sheafCartesianUnitIso a ha) (sheafCartesianCounitIso a ha)

/-- The forward functor of set-valued proper descent is cartesian inverse image. -/
theorem sheafCartesianEquivalence_functor (ha : IsProperHypercovering a) :
    (sheafCartesianEquivalence a ha).functor = sheafCartesianFunctor a :=
  rfl

/-- The inverse functor of set-valued proper descent is cartesian direct image. -/
theorem sheafCartesianEquivalence_inverse (ha : IsProperHypercovering a) :
    (sheafCartesianEquivalence a ha).inverse = sheafCartesianInverse a :=
  rfl

/-- The essential image of geometric inverse image along a proper hypercovering consists
exactly of cartesian sheaves of sets. -/
theorem sheaf_mem_essImage_iff_isCartesian (ha : IsProperHypercovering a)
    (G : Sheaf (zariskiTopology (forgetToTop.obj U)) (Type u)) :
    (LeftExactAdjunction.inverseImage (augmentationMorphism (toTopCatAugmentation a))).essImage G ↔
      IsCartesian (forgetToTop.obj U) (Type u) G :=
  sorry

/-- The functor `a⁻¹` corestricted to cartesian abelian sheaves. -/
def abelianCartesianFunctor :
    Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u} ⥤
      Cartesian (forgetToTop.obj U) AddCommGrpCat.{u} :=
  (cartesianProperty (forgetToTop.obj U) AddCommGrpCat.{u}).lift
    (inverseImage (toTopCatAugmentation a) AddCommGrpCat.{u})
    fun F ↦ inverseImage_isCartesian (toTopCatAugmentation a) AddCommGrpCat.{u} F

/-- On objects, `abelianCartesianFunctor` is inverse image along the Zariski
augmentation. -/
theorem abelianCartesianFunctor_obj
    (F : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u}) :
    ((abelianCartesianFunctor a).obj F).obj =
      (inverseImage (toTopCatAugmentation a) AddCommGrpCat.{u}).obj F :=
  rfl

/-- Direct image `a_*` on cartesian abelian sheaves. -/
def abelianCartesianInverse :
    Cartesian (forgetToTop.obj U) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u} :=
  (cartesianProperty (forgetToTop.obj U) AddCommGrpCat.{u}).ι ⋙
    directImage (toTopCatAugmentation a) AddCommGrpCat.{u}

/-- On objects, `abelianCartesianInverse` is direct image along the Zariski
augmentation. -/
theorem abelianCartesianInverse_obj
    (G : Cartesian (forgetToTop.obj U) AddCommGrpCat.{u}) :
    (abelianCartesianInverse a).obj G =
      (directImage (toTopCatAugmentation a) AddCommGrpCat.{u}).obj G.obj :=
  rfl

/-- The unit of `a⁻¹ ⊣ a_*` is an isomorphism on abelian sheaves along a proper
hypercovering. -/
theorem abelian_unit_app_isIso (ha : IsProperHypercovering a)
    (F : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u}) :
    IsIso ((inverseImageAdjunction (toTopCatAugmentation a) AddCommGrpCat.{u}).unit.app F) :=
  sorry

/-- The counit of `a⁻¹ ⊣ a_*` is an isomorphism on a cartesian abelian sheaf. -/
theorem abelian_counit_app_isIso_of_isCartesian (ha : IsProperHypercovering a)
    (G : Sheaf (zariskiTopology (forgetToTop.obj U)) AddCommGrpCat.{u})
    (h : IsCartesian (forgetToTop.obj U) AddCommGrpCat.{u} G) :
    IsIso ((inverseImageAdjunction (toTopCatAugmentation a) AddCommGrpCat.{u}).counit.app G) :=
  sorry

/-- Naturality of the unit components of abelian proper-hypercovering descent. -/
theorem abelianCartesianUnitIso_naturality (ha : IsProperHypercovering a)
    {F G : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u}} (f : F ⟶ G) :
    (𝟭 (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u})).map f ≫
        (@asIso _ _ _ _
          ((inverseImageAdjunction (toTopCatAugmentation a) AddCommGrpCat.{u}).unit.app G)
          (abelian_unit_app_isIso a ha G)).hom =
      (@asIso _ _ _ _
          ((inverseImageAdjunction (toTopCatAugmentation a) AddCommGrpCat.{u}).unit.app F)
          (abelian_unit_app_isIso a ha F)).hom ≫
        (abelianCartesianFunctor a ⋙ abelianCartesianInverse a).map f :=
  sorry

/-- The unit isomorphism `𝟭 ≅ a⁻¹ ⋙ a_*` of abelian proper hypercovering descent. -/
def abelianCartesianUnitIso (ha : IsProperHypercovering a) :
    𝟭 (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u}) ≅
      abelianCartesianFunctor a ⋙ abelianCartesianInverse a :=
  NatIso.ofComponents
    (fun F ↦
      @asIso _ _ _ _
        ((inverseImageAdjunction (toTopCatAugmentation a) AddCommGrpCat.{u}).unit.app F)
        (abelian_unit_app_isIso a ha F))
    (fun f ↦ abelianCartesianUnitIso_naturality a ha f)

/-- Naturality of the counit components of abelian proper-hypercovering descent. -/
theorem abelianCartesianCounitIso_naturality (ha : IsProperHypercovering a)
    {F G : Cartesian (forgetToTop.obj U) AddCommGrpCat.{u}} (f : F ⟶ G) :
    (abelianCartesianInverse a ⋙ abelianCartesianFunctor a).map f ≫
        ((cartesianProperty (forgetToTop.obj U) AddCommGrpCat.{u}).isoMk
          (@asIso _ _ _ _
            ((inverseImageAdjunction (toTopCatAugmentation a) AddCommGrpCat.{u}).counit.app G.obj)
            (abelian_counit_app_isIso_of_isCartesian a ha G.obj G.property))).hom =
      ((cartesianProperty (forgetToTop.obj U) AddCommGrpCat.{u}).isoMk
          (@asIso _ _ _ _
            ((inverseImageAdjunction (toTopCatAugmentation a) AddCommGrpCat.{u}).counit.app F.obj)
            (abelian_counit_app_isIso_of_isCartesian a ha F.obj F.property))).hom ≫
        (𝟭 (Cartesian (forgetToTop.obj U) AddCommGrpCat.{u})).map f :=
  sorry

/-- The counit isomorphism `a_* ⋙ a⁻¹ ≅ 𝟭` on cartesian abelian sheaves. -/
def abelianCartesianCounitIso (ha : IsProperHypercovering a) :
    abelianCartesianInverse a ⋙ abelianCartesianFunctor a ≅
      𝟭 (Cartesian (forgetToTop.obj U) AddCommGrpCat.{u}) :=
  NatIso.ofComponents
    (fun G ↦
      (cartesianProperty (forgetToTop.obj U) AddCommGrpCat.{u}).isoMk
        (@asIso _ _ _ _
          ((inverseImageAdjunction (toTopCatAugmentation a) AddCommGrpCat.{u}).counit.app G.obj)
          (abelian_counit_app_isIso_of_isCartesian a ha G.obj G.property)))
    (fun f ↦ abelianCartesianCounitIso_naturality a ha f)

/-- A proper hypercovering identifies abelian sheaves on its target with cartesian
abelian sheaves on its simplicial Zariski site, via augmentation inverse and direct image. -/
def abelianCartesianEquivalence (ha : IsProperHypercovering a) :
    Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u} ≌
      Cartesian (forgetToTop.obj U) AddCommGrpCat.{u} :=
  CategoryTheory.Equivalence.mk (abelianCartesianFunctor a) (abelianCartesianInverse a)
    (abelianCartesianUnitIso a ha) (abelianCartesianCounitIso a ha)

/-- The forward functor of `abelianCartesianEquivalence` is `a⁻¹` corestricted
to cartesian sheaves of abelian groups. -/
theorem abelianCartesianEquivalence_functor (ha : IsProperHypercovering a) :
    (abelianCartesianEquivalence a ha).functor = abelianCartesianFunctor a :=
  rfl

/-- The inverse functor of `abelianCartesianEquivalence` is `a_*` on cartesian
sheaves of abelian groups. -/
theorem abelianCartesianEquivalence_inverse (ha : IsProperHypercovering a) :
    (abelianCartesianEquivalence a ha).inverse = abelianCartesianInverse a :=
  rfl

/-- An abelian sheaf on `U_Zar` lies in the essential image of `a⁻¹` if and only
if it is cartesian. -/
theorem abelian_mem_essImage_iff_isCartesian (ha : IsProperHypercovering a)
    (G : Sheaf (zariskiTopology (forgetToTop.obj U)) AddCommGrpCat.{u}) :
    (inverseImage (toTopCatAugmentation a) AddCommGrpCat.{u}).essImage G ↔
      IsCartesian (forgetToTop.obj U) AddCommGrpCat.{u} G :=
  sorry

end LCCat

end
