/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_25_2_Cartesian
public import stacks_project.Chap85.Lemma_85_25_2_Equivalence
public import stacks_project.Chap85.Lemma_85_25_2_Hypercovering

/-!
# Lemma 85.25.2

If `a : U ⟶ X` is a proper hypercovering of an object `X` of `LCCat`, then
`a⁻¹` on sheaves of sets and on abelian sheaves is fully faithful with
essential image the cartesian sheaves, and with quasi-inverse `a_*`.
Here `a` is the Lemma 85.2.8 Zariski augmentation morphism.
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

/-- The Lemma 85.2.8 inverse image `a⁻¹` on sheaves of sets. -/
def zariskiAugmentationInverseImage :
    Sheaf (Opens.grothendieckTopology X.obj) (Type u) ⥤
      Sheaf (zariskiTopology (forgetToTop.obj U)) (Type u) :=
  LeftExactAdjunction.inverseImage (augmentationMorphism (toTopCatAugmentation a))

/-- `zariskiAugmentationInverseImage` is the inverse image of the Lemma 85.2.8
Zariski augmentation morphism. -/
theorem zariskiAugmentationInverseImage_eq :
    zariskiAugmentationInverseImage a =
      LeftExactAdjunction.inverseImage (augmentationMorphism (toTopCatAugmentation a)) :=
  sorry

/-- The functor `a⁻¹` of Lemma 85.2.8, corestricted to cartesian sheaves of sets. -/
def sheafCartesianFunctor :
    Sheaf (Opens.grothendieckTopology X.obj) (Type u) ⥤
      Cartesian (forgetToTop.obj U) (Type u) :=
  (cartesianProperty (forgetToTop.obj U) (Type u)).lift
    (zariskiAugmentationInverseImage a)
    fun F ↦ augmentationMorphism_inverseImage_isCartesian (toTopCatAugmentation a) F

/-- On objects, `sheafCartesianFunctor` is the Lemma 85.2.8 inverse image. -/
theorem sheafCartesianFunctor_obj
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type u)) :
    ((sheafCartesianFunctor a).obj F).obj = (zariskiAugmentationInverseImage a).obj F :=
  sorry

/-- Direct image `a_*` of the Lemma 85.2.8 Zariski augmentation, on cartesian sheaves of
sets. -/
def sheafCartesianInverse :
    Cartesian (forgetToTop.obj U) (Type u) ⥤
      Sheaf (Opens.grothendieckTopology X.obj) (Type u) :=
  (cartesianProperty (forgetToTop.obj U) (Type u)).ι ⋙
    (augmentationMorphism (toTopCatAugmentation a)).pushforward

/-- On objects, `sheafCartesianInverse` is the Lemma 85.2.8 direct image. -/
theorem sheafCartesianInverse_obj (G : Cartesian (forgetToTop.obj U) (Type u)) :
    (sheafCartesianInverse a).obj G =
      (augmentationMorphism (toTopCatAugmentation a)).pushforward.obj G.obj :=
  sorry

/-- The unit of the Lemma 85.2.8 adjunction is an isomorphism along a proper
hypercovering. -/
theorem sheaf_unit_app_isIso (ha : IsProperHypercovering a)
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type u)) :
    IsIso ((augmentationMorphism (toTopCatAugmentation a)).adjunction.unit.app F) :=
  sorry

/-- The counit of the Lemma 85.2.8 adjunction is an isomorphism on a cartesian sheaf of
sets. -/
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

/-- Lemma 85.25.2 (1). Let `U` be a simplicial object of `LCCat` and let
`a : U ⟶ X` be an augmentation. If `a` is a proper hypercovering of `X`, then
`a⁻¹ : Sh(X) ⥤ Sh(U_Zar)` is fully faithful with essential image the cartesian
sheaves of sets, and `a_*` provides the quasi-inverse. Here `a` is the
Lemma 85.2.8 Zariski augmentation `augmentationMorphism (toTopCatAugmentation a)`. -/
@[stacks 0DAG]
def sheafCartesianEquivalence (ha : IsProperHypercovering a) :
    Sheaf (Opens.grothendieckTopology X.obj) (Type u) ≌
      Cartesian (forgetToTop.obj U) (Type u) :=
  CategoryTheory.Equivalence.mk (sheafCartesianFunctor a) (sheafCartesianInverse a)
    (sheafCartesianUnitIso a ha) (sheafCartesianCounitIso a ha)

/-- The forward functor of `sheafCartesianEquivalence` is the Lemma 85.2.8 inverse
image `a⁻¹`, corestricted to cartesian sheaves of sets. -/
theorem sheafCartesianEquivalence_functor (ha : IsProperHypercovering a) :
    (sheafCartesianEquivalence a ha).functor = sheafCartesianFunctor a :=
  sorry

/-- The inverse functor of `sheafCartesianEquivalence` is `a_*` on cartesian
sheaves of sets, for the Lemma 85.2.8 Zariski augmentation. -/
theorem sheafCartesianEquivalence_inverse (ha : IsProperHypercovering a) :
    (sheafCartesianEquivalence a ha).inverse = sheafCartesianInverse a :=
  sorry

/-- A sheaf of sets on `U_Zar` lies in the essential image of the Lemma 85.2.8
inverse image `a⁻¹` if and only if it is cartesian. -/
theorem sheaf_mem_essImage_iff_isCartesian (ha : IsProperHypercovering a)
    (G : Sheaf (zariskiTopology (forgetToTop.obj U)) (Type u)) :
    (zariskiAugmentationInverseImage a).essImage G ↔
      IsCartesian (forgetToTop.obj U) (Type u) G :=
  sorry

/-- Inverse image of sheaves of sets along the parallel composite is canonically
isomorphic to the Lemma 85.2.8 inverse image, via `constInverseImageIso` on the
`constProjection` factor. -/
def sheafCartesianEquivalence_inverseImage :
    inverseImage (toTopCatAugmentation a) (Type u) ≅
      zariskiAugmentationInverseImage a :=
  inverseImageIso_augmentation (toTopCatAugmentation a)

/-- The forward map of `sheafCartesianEquivalence_inverseImage` is the whiskered
`constInverseImageIso` comparison of `inverseImageIso_augmentation`. -/
theorem sheafCartesianEquivalence_inverseImage_hom :
    (sheafCartesianEquivalence_inverseImage a).hom =
      (inverseImageIso_augmentation (toTopCatAugmentation a)).hom :=
  sorry

/-- Inverse image `a⁻¹` on abelian sheaves along the Zariski augmentation. -/
def abelianInverseImage :
    Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u} ⥤
      Sheaf (zariskiTopology (forgetToTop.obj U)) AddCommGrpCat.{u} :=
  inverseImage (toTopCatAugmentation a) AddCommGrpCat.{u}

/-- `abelianInverseImage` is inverse image along the Zariski augmentation. -/
theorem abelianInverseImage_eq :
    abelianInverseImage a = inverseImage (toTopCatAugmentation a) AddCommGrpCat.{u} :=
  sorry

/-- The functor `a⁻¹` corestricted to cartesian abelian sheaves. -/
def abelianCartesianFunctor :
    Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u} ⥤
      Cartesian (forgetToTop.obj U) AddCommGrpCat.{u} :=
  (cartesianProperty (forgetToTop.obj U) AddCommGrpCat.{u}).lift
    (abelianInverseImage a)
    fun F ↦ inverseImage_isCartesian (toTopCatAugmentation a) AddCommGrpCat.{u} F

/-- On objects, `abelianCartesianFunctor` is inverse image along the Zariski
augmentation. -/
theorem abelianCartesianFunctor_obj
    (F : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u}) :
    ((abelianCartesianFunctor a).obj F).obj = (abelianInverseImage a).obj F :=
  sorry

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
  sorry

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

/-- Lemma 85.25.2 (2). Let `U` be a simplicial object of `LCCat` and let
`a : U ⟶ X` be an augmentation. If `a` is a proper hypercovering of `X`, then
`a⁻¹ : Ab(X) ⥤ Ab(U_Zar)` is fully faithful with essential image the cartesian
sheaves of abelian groups, and `a_*` provides the quasi-inverse. Here `a` is the
Lemma 85.2.8 Zariski augmentation `augmentationMorphism (toTopCatAugmentation a)`. -/
@[stacks 0DAG]
def abelianCartesianEquivalence (ha : IsProperHypercovering a) :
    Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{u} ≌
      Cartesian (forgetToTop.obj U) AddCommGrpCat.{u} :=
  CategoryTheory.Equivalence.mk (abelianCartesianFunctor a) (abelianCartesianInverse a)
    (abelianCartesianUnitIso a ha) (abelianCartesianCounitIso a ha)

/-- The forward functor of `abelianCartesianEquivalence` is `a⁻¹` corestricted
to cartesian sheaves of abelian groups. -/
theorem abelianCartesianEquivalence_functor (ha : IsProperHypercovering a) :
    (abelianCartesianEquivalence a ha).functor = abelianCartesianFunctor a :=
  sorry

/-- The inverse functor of `abelianCartesianEquivalence` is `a_*` on cartesian
sheaves of abelian groups. -/
theorem abelianCartesianEquivalence_inverse (ha : IsProperHypercovering a) :
    (abelianCartesianEquivalence a ha).inverse = abelianCartesianInverse a :=
  sorry

/-- An abelian sheaf on `U_Zar` lies in the essential image of `a⁻¹` if and only
if it is cartesian. -/
theorem abelian_mem_essImage_iff_isCartesian (ha : IsProperHypercovering a)
    (G : Sheaf (zariskiTopology (forgetToTop.obj U)) AddCommGrpCat.{u}) :
    (abelianInverseImage a).essImage G ↔
      IsCartesian (forgetToTop.obj U) AddCommGrpCat.{u} G :=
  sorry

end LCCat

end
