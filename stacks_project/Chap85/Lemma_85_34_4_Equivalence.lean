module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Flat
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import stacks_project.Chap85.Lemma_85_34_3_Derived
public import stacks_project.Chap85.Lemma_85_34_4_DerivedQCoh

/-!
# Derived QCoh descent along an fppf hypercovering

If `a : U ⟶ X` is an fppf hypercovering, the restricted derived functors
`a^*` and `Ra_*` implement an equivalence `D_QCoh(𝒪_X) ≌ D_QCoh(𝒪_U)` on the
Section 85.32 spaces-étale sites.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open Functor
open RingedSite.Hom
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- The total left-derived functor of module pullback along the spaces-étale
augmentation exists at carrier universe `u + 1`. -/
instance hasLeftDerived_modulePullbackToDerived :
    Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{u + 1} (spacesEtaleAugmentationHom a))
      (ModuleQis.{u + 1} (spacesRingedSite X)) :=
  sorry

/-- The total derived pair condition for `a^* ⊣ Ra_*` holds along the spaces-étale
augmentation at carrier universe `u + 1`. -/
instance derivedAdjunction_hasPair :
    DerivedAdjunction.HasPair.{u + 1} (spacesEtaleAugmentationHom a) :=
  sorry

/-- The spaces-étale augmentation of an fppf hypercovering is flat at carrier
universe `u + 1`. -/
instance spacesEtaleAugmentationHom_isFlat (ha : IsFppfHypercovering a) :
    let _ := ha
    IsFlat.{u + 1} (spacesEtaleAugmentationHom a) :=
  sorry

/-- The derived adjunction `a^* ⊣ Ra_*` of modules along the spaces-étale
augmentation. -/
abbrev derivedModuleAdjunction :
    modulePullbackDerived.{u + 1} (spacesEtaleAugmentationHom a) ⊣
      modulePushforwardDerived.{u + 1} (spacesEtaleAugmentationHom a) :=
  moduleDerivedAdjunction.{u + 1} (spacesEtaleAugmentationHom a)

/-- `derivedModuleAdjunction a` is the Hom-level derived module adjunction of
`spacesEtaleAugmentationHom a`. -/
theorem derivedModuleAdjunction_eq :
    derivedModuleAdjunction a =
      moduleDerivedAdjunction.{u + 1} (spacesEtaleAugmentationHom a) :=
  sorry

/-- Derived pullback along the spaces-étale augmentation preserves quasi-coherent
cohomology. -/
theorem modulePullbackDerived_le_inverseImage :
    moduleCohomologyIn.{u + 1} (spacesRingedSite X) (spacesQuasiCoherentProperty X) ≤
      (moduleCohomologyIn.{u + 1} (etaleTotalRingedSite U)
          (quasiCoherentProperty U)).inverseImage
        (modulePullbackDerived.{u + 1} (spacesEtaleAugmentationHom a)) :=
  sorry

/-- If `a` is an fppf hypercovering, derived pushforward along the spaces-étale
augmentation preserves quasi-coherent cohomology. -/
theorem modulePushforwardDerived_le_inverseImage (ha : IsFppfHypercovering a) :
    moduleCohomologyIn.{u + 1} (etaleTotalRingedSite U) (quasiCoherentProperty U) ≤
      (moduleCohomologyIn.{u + 1} (spacesRingedSite X)
          (spacesQuasiCoherentProperty X)).inverseImage
        (modulePushforwardDerived.{u + 1} (spacesEtaleAugmentationHom a)) :=
  sorry

namespace DerivedQCoh

/-- Restriction of derived inverse image `a^*` to `D_QCoh`. -/
def pullback : spacesDerivedQCoh X ⥤ DerivedQCoh U :=
  FullSubcategory.restrict
    (modulePullbackDerived.{u + 1} (spacesEtaleAugmentationHom a))
    (modulePullbackDerived_le_inverseImage a)

/-- The underlying derived module of `DerivedQCoh.pullback a` is derived module
pullback along the spaces-étale augmentation. -/
theorem pullback_obj (F : spacesDerivedQCoh X) :
    ((pullback a).obj F).obj =
      (modulePullbackDerived.{u + 1} (spacesEtaleAugmentationHom a)).obj F.obj :=
  sorry

/-- Restriction of derived direct image `Ra_*` to `D_QCoh`, when `a` is an fppf
hypercovering. -/
def pushforward (ha : IsFppfHypercovering a) :
    DerivedQCoh U ⥤ spacesDerivedQCoh X :=
  FullSubcategory.restrict
    (modulePushforwardDerived.{u + 1} (spacesEtaleAugmentationHom a))
    (modulePushforwardDerived_le_inverseImage a ha)

/-- The underlying derived module of `DerivedQCoh.pushforward a ha` is derived
module pushforward along the spaces-étale augmentation. -/
theorem pushforward_obj (ha : IsFppfHypercovering a) (G : DerivedQCoh U) :
    ((pushforward a ha).obj G).obj =
      (modulePushforwardDerived.{u + 1} (spacesEtaleAugmentationHom a)).obj G.obj :=
  sorry

end DerivedQCoh

/-- The unit of `a^* ⊣ Ra_*` is an isomorphism on an object of `D_QCoh(𝒪_X)`. -/
theorem unit_app_isIso (ha : IsFppfHypercovering a) (F : spacesDerivedQCoh X) :
    IsIso ((derivedModuleAdjunction a).unit.app F.obj) :=
  sorry

/-- The counit of `a^* ⊣ Ra_*` is an isomorphism on an object of `D_QCoh(𝒪_U)`. -/
theorem counit_app_isIso (ha : IsFppfHypercovering a) (G : DerivedQCoh U) :
    IsIso ((derivedModuleAdjunction a).counit.app G.obj) :=
  sorry

/-- The component of the derived QCoh unit isomorphism at `F`. -/
def derivedQCohUnitIsoApp (ha : IsFppfHypercovering a) (F : spacesDerivedQCoh X) :
    F ≅ (DerivedQCoh.pullback a ⋙ DerivedQCoh.pushforward a ha).obj F :=
  (moduleCohomologyIn.{u + 1} (spacesRingedSite X)
      (spacesQuasiCoherentProperty X)).isoMk
    (@asIso _ _ _ _ ((derivedModuleAdjunction a).unit.app F.obj)
      (unit_app_isIso a ha F))

/-- Naturality of the unit components of derived QCoh descent. -/
theorem derivedQCohUnitIso_naturality (ha : IsFppfHypercovering a)
    {F G : spacesDerivedQCoh X} (f : F ⟶ G) :
    (𝟭 (spacesDerivedQCoh X)).map f ≫ (derivedQCohUnitIsoApp a ha G).hom =
      (derivedQCohUnitIsoApp a ha F).hom ≫
        (DerivedQCoh.pullback a ⋙ DerivedQCoh.pushforward a ha).map f :=
  sorry

/-- The unit isomorphism `𝟭 ≅ a^* ⋙ Ra_*` of fppf hypercovering descent on
`D_QCoh`. -/
def derivedQCohUnitIso (ha : IsFppfHypercovering a) :
    𝟭 (spacesDerivedQCoh X) ≅
      DerivedQCoh.pullback a ⋙ DerivedQCoh.pushforward a ha :=
  NatIso.ofComponents (fun F ↦ derivedQCohUnitIsoApp a ha F)
    (fun f ↦ derivedQCohUnitIso_naturality a ha f)

/-- The component of `derivedQCohUnitIso` at `F` is the derived adjunction unit on
the underlying object. -/
theorem derivedQCohUnitIso_hom_app_hom (ha : IsFppfHypercovering a)
    (F : spacesDerivedQCoh X) :
    ((derivedQCohUnitIso a ha).hom.app F).hom =
      (derivedModuleAdjunction a).unit.app F.obj :=
  sorry

/-- The component of the derived QCoh counit isomorphism at `G`. -/
def derivedQCohCounitIsoApp (ha : IsFppfHypercovering a) (G : DerivedQCoh U) :
    (DerivedQCoh.pushforward a ha ⋙ DerivedQCoh.pullback a).obj G ≅ G :=
  (moduleCohomologyIn.{u + 1} (etaleTotalRingedSite U)
      (quasiCoherentProperty U)).isoMk
    (@asIso _ _ _ _ ((derivedModuleAdjunction a).counit.app G.obj)
      (counit_app_isIso a ha G))

/-- Naturality of the counit components of derived QCoh descent. -/
theorem derivedQCohCounitIso_naturality (ha : IsFppfHypercovering a)
    {F G : DerivedQCoh U} (f : F ⟶ G) :
    (DerivedQCoh.pushforward a ha ⋙ DerivedQCoh.pullback a).map f ≫
        (derivedQCohCounitIsoApp a ha G).hom =
      (derivedQCohCounitIsoApp a ha F).hom ≫ (𝟭 (DerivedQCoh U)).map f :=
  sorry

/-- The counit isomorphism `Ra_* ⋙ a^* ≅ 𝟭` on `D_QCoh(𝒪_U)`. -/
def derivedQCohCounitIso (ha : IsFppfHypercovering a) :
    DerivedQCoh.pushforward a ha ⋙ DerivedQCoh.pullback a ≅ 𝟭 (DerivedQCoh U) :=
  NatIso.ofComponents (fun G ↦ derivedQCohCounitIsoApp a ha G)
    (fun f ↦ derivedQCohCounitIso_naturality a ha f)

/-- The component of `derivedQCohCounitIso` at `G` is the derived adjunction counit
on the underlying object. -/
theorem derivedQCohCounitIso_hom_app_hom (ha : IsFppfHypercovering a)
    (G : DerivedQCoh U) :
    ((derivedQCohCounitIso a ha).hom.app G).hom =
      (derivedModuleAdjunction a).counit.app G.obj :=
  sorry

/-- If `a` is an fppf hypercovering of `X`, then `a^*` implements an equivalence
between `D_QCoh(𝒪_X)` and `D_QCoh(𝒪_U)`, with quasi-inverse `Ra_*`. -/
def derivedQCohDescent (ha : IsFppfHypercovering a) :
    spacesDerivedQCoh X ≌ DerivedQCoh U :=
  CategoryTheory.Equivalence.mk (DerivedQCoh.pullback a) (DerivedQCoh.pushforward a ha)
    (derivedQCohUnitIso a ha) (derivedQCohCounitIso a ha)

/-- The forward functor of `derivedQCohDescent` is `a^*` on `D_QCoh`. -/
theorem derivedQCohDescent_functor (ha : IsFppfHypercovering a) :
    (derivedQCohDescent a ha).functor = DerivedQCoh.pullback a :=
  sorry

/-- The inverse functor of `derivedQCohDescent` is `Ra_*` on `D_QCoh`. -/
theorem derivedQCohDescent_inverse (ha : IsFppfHypercovering a) :
    (derivedQCohDescent a ha).inverse = DerivedQCoh.pushforward a ha :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
