module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import stacks_project.Chap73.Lemma_73_4_8_Identity
public import stacks_project.Chap84.«84_5_2_1_Site»
public import stacks_project.Chap84.Lemma_84_6_4_Comparison
public import stacks_project.Chap85.Lemma_85_21_5_Augmentation
public import stacks_project.Chap85.Lemma_85_33_1_Etale

/-!
# Fppf–étale comparison square for a simplicial algebraic space

The identity-on-objects inclusions of spaces-étale sites into fppf slice sites,
together with the Case A augmentations of `U` and `X`, present a commutative
square of morphisms of topoi
`Sh((Spaces/U)_fppf,total) ⟶ Sh(U_spaces,étale)` over
`Sh((Spaces/X)_fppf) ⟶ Sh(X_spaces,étale)`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.SimplicialObject
open scoped Simplicial MorphismOfTopoiIn

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} (U : SimplicialObject (AlgebraicSpace S))

/-- Fibre of `toSliceTotal` at an object of `SpacesEtale U`. -/
def toSliceTotalObj (Y : SpacesEtale U) : sliceTotalSite U :=
  ⟨Y.index, Over.mk Y.obj.hom⟩

/-- The Grothendieck fibre of a commutative-square morphism. -/
def toSliceTotalMap_fiber {Y Z : SpacesEtale U} (f : Y ⟶ Z) :
    ((sliceDiagram U).map f.simplex.op).toFunctor.obj (Over.mk Y.obj.hom) ⟶
      Over.mk Z.obj.hom :=
  Over.homMk f.hom f.w

/-- The morphism of Grothendieck objects associated to a commutative square. -/
def toSliceTotalMap {Y Z : SpacesEtale U} (f : Y ⟶ Z) :
    toSliceTotalObj U Y ⟶ toSliceTotalObj U Z where
  base := f.simplex.op
  fiber := toSliceTotalMap_fiber U f

/-- The presenting functor of the top horizontal arrow: send an étale object over
`U.obj n` to the same morphism viewed in `(Spaces/U_n)_fppf`, as an object of
`(Spaces/U)_{fppf,total}`. -/
def toSliceTotal : SpacesEtale U ⥤ sliceTotalSite U where
  obj Y := toSliceTotalObj U Y
  map f := toSliceTotalMap U f
  map_id := sorry
  map_comp := sorry

/-- On objects, `toSliceTotal U` is the Grothendieck object with the same degree and
structure morphism. -/
theorem toSliceTotal_obj (Y : SpacesEtale U) :
    (toSliceTotal U).obj Y = ⟨Y.index, Over.mk Y.obj.hom⟩ :=
  rfl

/-- On morphisms, `toSliceTotal U` is the Grothendieck arrow with base `f.simplex.op`
and fibre `Over.homMk f.hom f.w`. -/
theorem toSliceTotal_map {Y Z : SpacesEtale U} (f : Y ⟶ Z) :
    (toSliceTotal U).map f = toSliceTotalMap U f :=
  rfl

/-- The inclusion `SpacesEtale U ⥤ sliceTotalSite U` is continuous for the total
spaces-étale and fppf topologies. -/
instance toSliceTotal_isContinuous :
    (toSliceTotal U).IsContinuous (spacesEtaleTotalTopology U)
      (sliceTotalTopology (fppfTopology S) U) :=
  sorry

/-- Opposite of `toSliceTotal U` admits left Kan extensions of type-valued
presheaves. -/
instance toSliceTotal_op_hasLeftKanExtension
    (P : (SpacesEtale U)ᵒᵖ ⥤ Type (u + 1)) :
    (toSliceTotal U).op.HasLeftKanExtension P :=
  sorry

/-- Sheaves of types in universe `u + 1` on `(Spaces/U)_{fppf,total}` admit
sheafification. -/
instance hasSheafify_sliceTotalTopology_fppf :
    HasSheafify (sliceTotalTopology (fppfTopology S) U) (Type (u + 1)) :=
  sorry

/-- Sheaf pullback along `toSliceTotal U` preserves finite limits. -/
instance toSliceTotal_sheafPullback_preservesFiniteLimits :
    PreservesFiniteLimits
      ((toSliceTotal U).sheafPullback (Type (u + 1))
        (spacesEtaleTotalTopology U) (sliceTotalTopology (fppfTopology S) U)) :=
  sorry

/-- The presenting functor of the top horizontal arrow is an exact morphism of
sites. -/
instance toSliceTotal_isExactMorphismOfSites :
    IsExactMorphismOfSites.{u + 1, u + 1, u + 1, u + 1, u + 1}
      (spacesEtaleTotalTopology U) (sliceTotalTopology (fppfTopology S) U)
      (toSliceTotal U) :=
  sorry

/-- The top horizontal morphism of topoi
`h : Sh((Spaces/U)_{fppf,total}) ⟶ Sh(U_spaces,étale)` presented by
`toSliceTotal`. -/
def fppfEtaleComparison :
    MorphismOfTopoiIn (spacesEtaleTotalTopology U)
      (sliceTotalTopology (fppfTopology S) U) :=
  (toSliceTotal U).morphismOfTopoiInOfContinuous.{u + 1, u + 1, u + 1, u + 1, u + 1}
    (spacesEtaleTotalTopology U) (sliceTotalTopology (fppfTopology S) U)

/-- Inverse image of `fppfEtaleComparison U` is sheaf pullback along
`toSliceTotal U`. -/
theorem fppfEtaleComparison_inverseImage :
    (fppfEtaleComparison U)⁻¹ =
      (toSliceTotal U).sheafPullback (Type (u + 1))
        (spacesEtaleTotalTopology U) (sliceTotalTopology (fppfTopology S) U) :=
  sorry

variable (X : AlgebraicSpace S)

/-- Sheaves of types in universe `u + 1` on `(Spaces/X)_fppf` admit sheafification. -/
instance hasSheafify_overFppfTopology : HasSheafify (overFppfTopology X) (Type (u + 1)) :=
  sorry

/-- The forgetful functor `X_spaces,étale ⥤ (Spaces/X)_fppf` is continuous. -/
instance spacesEtaleToBig_isContinuous_fppf :
    (Etale.SmallToBig.spacesEtaleToBig X).IsContinuous
      (spacesEtaleTopology X) (overFppfTopology X) :=
  sorry

/-- Opposite of `spacesEtaleToBig X` admits left Kan extensions into the big fppf
site. -/
instance spacesEtaleToBig_op_hasLeftKanExtension_fppf
    (P : (spacesEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) :
    (Etale.SmallToBig.spacesEtaleToBig X).op.HasLeftKanExtension P :=
  sorry

/-- Sheaf pullback along `spacesEtaleToBig X` into the big fppf topos preserves
finite limits. -/
instance spacesEtaleToBig_sheafPullback_preservesFiniteLimits_fppf :
    PreservesFiniteLimits
      ((Etale.SmallToBig.spacesEtaleToBig X).sheafPullback (Type (u + 1))
        (spacesEtaleTopology X) (overFppfTopology X)) :=
  sorry

/-- The forgetful functor `X_spaces,étale ⥤ (Spaces/X)_fppf` is an exact morphism of
sites. -/
instance spacesEtaleToBig_isExactMorphismOfSites_fppf :
    IsExactMorphismOfSites.{u + 1, u + 1, u + 1, u + 1, u + 1}
      (spacesEtaleTopology X) (overFppfTopology X)
      (Etale.SmallToBig.spacesEtaleToBig X) :=
  sorry

/-- The bottom horizontal morphism of topoi
`h₋₁ : Sh((Spaces/X)_fppf) ⟶ Sh(X_spaces,étale)` presented by `U ↦ U / X`.
This is the spaces-étale form of `a_X = π_X ∘ ε_X`. -/
def spacesFppfComparison :
    MorphismOfTopoiIn (spacesEtaleTopology X) (overFppfTopology X) :=
  (Etale.SmallToBig.spacesEtaleToBig X).morphismOfTopoiInOfContinuous.{u + 1, u + 1, u + 1, u + 1, u + 1}
    (spacesEtaleTopology X) (overFppfTopology X)

/-- Inverse image of `spacesFppfComparison X` is sheaf pullback along
`spacesEtaleToBig X`. -/
theorem spacesFppfComparison_inverseImage :
    (spacesFppfComparison X)⁻¹ =
      (Etale.SmallToBig.spacesEtaleToBig X).sheafPullback (Type (u + 1))
        (spacesEtaleTopology X) (overFppfTopology X) :=
  sorry

/-- Restriction of `spacesFppfComparison` along `smallEtaleInclusion` recovers the
small-étale comparison `a_X = π_X ∘ ε_X`. -/
theorem spacesFppfComparison_comp_small :
    smallEtaleInclusion X ⋙ Etale.SmallToBig.spacesEtaleToBig X =
      Etale.SmallToBig.smallEtaleToBig X :=
  rfl

variable {X : AlgebraicSpace S} (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X)

/-- Opposite of the Case A fppf augmentation functor admits left Kan extensions. -/
instance sliceAugmentationPullback_op_hasLeftKanExtension_fppf
    (P : (Over X)ᵒᵖ ⥤ Type (u + 1)) :
    (sliceAugmentationPullback U a).op.HasLeftKanExtension P :=
  sorry

/-- Sheaf pullback along `sliceAugmentationPullback` into the fppf total topos
preserves finite limits. -/
instance sliceAugmentationPullback_sheafPullback_preservesFiniteLimits_fppf :
    PreservesFiniteLimits
      ((sliceAugmentationPullback U a).sheafPullback (Type (u + 1))
        (overFppfTopology X) (sliceTotalTopology (fppfTopology S) U)) :=
  sorry

/-- The Case A fppf slice-augmentation is an exact morphism of sites. -/
instance sliceAugmentationPullback_isExactMorphismOfSites_fppf :
    IsExactMorphismOfSites.{u + 1, u + 1, u + 1, u + 1, u + 1}
      (overFppfTopology X) (sliceTotalTopology (fppfTopology S) U)
      (sliceAugmentationPullback U a) :=
  sorry

/-- The left vertical morphism of topoi
`a_fppf : Sh((Spaces/U)_{fppf,total}) ⟶ Sh((Spaces/X)_fppf)`, presented by the
Case A continuous functor of Section 85.21. -/
def fppfAugmentation :
    MorphismOfTopoiIn (overFppfTopology X) (sliceTotalTopology (fppfTopology S) U) :=
  (sliceAugmentationPullback U a).morphismOfTopoiInOfContinuous.{u + 1, u + 1, u + 1, u + 1, u + 1}
    (overFppfTopology X) (sliceTotalTopology (fppfTopology S) U)

/-- Inverse image of `fppfAugmentation a` is sheaf pullback along
`sliceAugmentationPullback`. -/
theorem fppfAugmentation_eq :
    (fppfAugmentation U a)⁻¹ =
      (sliceAugmentationPullback U a).sheafPullback (Type (u + 1))
        (overFppfTopology X) (sliceTotalTopology (fppfTopology S) U) :=
  sorry

/-- On objects, the two presenting composites of the source square agree: both send
`V` étale over `X` to the degree-zero object `V ×_X U_0` in the fppf total site. -/
theorem presentingCommSq_obj (V : spacesEtaleSite X) :
    (augmentationFunctor U a ⋙ toSliceTotal U).obj V =
      (Etale.SmallToBig.spacesEtaleToBig X ⋙ sliceAugmentationPullback U a).obj V :=
  rfl

/-- The objectwise identification of presenting composites, as the identity on the
common degree-zero pullback object. -/
def presentingCommSq_app (V : spacesEtaleSite X) :
    (augmentationFunctor U a ⋙ toSliceTotal U).obj V ≅
      (Etale.SmallToBig.spacesEtaleToBig X ⋙ sliceAugmentationPullback U a).obj V :=
  Iso.refl _

/-- Naturality of `presentingCommSq_app`. -/
theorem presentingCommSq_naturality {V W : spacesEtaleSite X} (f : V ⟶ W) :
    (augmentationFunctor U a ⋙ toSliceTotal U).map f ≫ (presentingCommSq_app U a W).hom =
      (presentingCommSq_app U a V).hom ≫
        (Etale.SmallToBig.spacesEtaleToBig X ⋙ sliceAugmentationPullback U a).map f :=
  sorry

/-- The left presenting composite of the source square is continuous. -/
instance augmentationFunctor_comp_toSliceTotal_isContinuous :
    (augmentationFunctor U a ⋙ toSliceTotal U).IsContinuous
      (spacesEtaleTopology X) (sliceTotalTopology (fppfTopology S) U) :=
  sorry

/-- Opposite of the left presenting composite admits left Kan extensions. -/
instance augmentationFunctor_comp_toSliceTotal_op_hasLeftKanExtension
    (P : (spacesEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) :
    (augmentationFunctor U a ⋙ toSliceTotal U).op.HasLeftKanExtension P :=
  sorry

/-- The right presenting composite of the source square is continuous. -/
instance spacesEtaleToBig_comp_sliceAugmentationPullback_isContinuous :
    (Etale.SmallToBig.spacesEtaleToBig X ⋙ sliceAugmentationPullback U a).IsContinuous
      (spacesEtaleTopology X) (sliceTotalTopology (fppfTopology S) U) :=
  sorry

/-- Opposite of the right presenting composite admits left Kan extensions. -/
instance spacesEtaleToBig_comp_sliceAugmentationPullback_op_hasLeftKanExtension
    (P : (spacesEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) :
    (Etale.SmallToBig.spacesEtaleToBig X ⋙ sliceAugmentationPullback U a).op.HasLeftKanExtension
      P :=
  sorry

/-- The presenting-functor square: pullback along `a0` then include into the fppf
total site agrees with forget-to-`Over X` then `sliceAugmentationPullback`. -/
def presentingCommSq :
    augmentationFunctor U a ⋙ toSliceTotal U ≅
      Etale.SmallToBig.spacesEtaleToBig X ⋙ sliceAugmentationPullback U a :=
  NatIso.ofComponents (presentingCommSq_app U a) (fun f ↦ presentingCommSq_naturality U a f)

/-- Inverse-image form of the commutative square of morphisms of topoi in
Lemma 85.33.1: `(a)⁻¹ ⋙ h⁻¹ ≅ (h₋₁)⁻¹ ⋙ (a_fppf)⁻¹`. -/
def fppfEtaleCommSq :
    (spacesEtaleAugmentation U a)⁻¹ ⋙ (fppfEtaleComparison U)⁻¹ ≅
      (spacesFppfComparison X)⁻¹ ⋙ (fppfAugmentation U a)⁻¹ :=
  Adjunction.leftAdjointCompIso
    ((augmentationFunctor U a).sheafAdjunctionContinuous (Type (u + 1))
      (spacesEtaleTopology X) (spacesEtaleTotalTopology U))
    ((toSliceTotal U).sheafAdjunctionContinuous (Type (u + 1))
      (spacesEtaleTotalTopology U) (sliceTotalTopology (fppfTopology S) U))
    (((Etale.SmallToBig.spacesEtaleToBig X).sheafAdjunctionContinuous (Type (u + 1))
        (spacesEtaleTopology X) (overFppfTopology X)).comp
      ((sliceAugmentationPullback U a).sheafAdjunctionContinuous (Type (u + 1))
        (overFppfTopology X) (sliceTotalTopology (fppfTopology S) U)))
    (Functor.sheafPushforwardContinuousComp' (presentingCommSq U a) (Type (u + 1))
      (spacesEtaleTopology X) (spacesEtaleTotalTopology U)
      (sliceTotalTopology (fppfTopology S) U))

/-- The two composite inverse images around `fppfEtaleCommSq` are inverse. -/
theorem fppfEtaleCommSq_hom_comp_inv :
    (fppfEtaleCommSq U a).hom ≫ (fppfEtaleCommSq U a).inv = 𝟙 _ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
