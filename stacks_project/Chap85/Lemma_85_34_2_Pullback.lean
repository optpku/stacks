module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import stacks_project.Chap85.Lemma_85_33_2_Hypercovering
public import stacks_project.Chap85.Lemma_85_34_1_Comparison
public import stacks_project.Chap85.Lemma_85_34_2_QCoh

/-!
# Pullback and pushforward of quasi-coherent modules along a spaces-étale augmentation

The Section 85.32 morphism of ringed topoi `spacesEtaleAugmentationRinged` induces
module functors `a^*` and `a_*`. Inverse image preserves quasi-coherence; if `a` is
an fppf hypercovering, then so does direct image, and both restrict to `QCoh`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open Functor
open RingedSite RingedSite.ToposHom
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- Restriction of scalars along the inverse-image structure map of the spaces-étale
augmentation is a right adjoint, so module pullback exists. -/
instance restrictScalars_structureMap_isRightAdjoint :
    (SheafOfModules.restrictScalars.{u}
      (spacesEtaleAugmentationRinged U a).structureMap).IsRightAdjoint :=
  sorry

/-- Abelian-group-valued sheaf composition exists on every slice of the spaces-étale
ringed site of an algebraic space. -/
instance hasSheafCompose_spacesRingedSite_over :
    ∀ x, ((spacesRingedSite X).siteTopology.over x).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  sorry

/-- Weak sheafification of abelian groups exists on every slice of the spaces-étale
ringed site of an algebraic space. -/
instance hasWeakSheafify_spacesRingedSite_over :
    ∀ x, HasWeakSheafify ((spacesRingedSite X).siteTopology.over x)
      AddCommGrpCat.{u} :=
  sorry

/-- Sheafification equivalences on slices of the spaces-étale ringed site of an
algebraic space are exactly the locally bijective morphisms. -/
instance wEqualsLocallyBijective_spacesRingedSite_over :
    ∀ x, ((spacesRingedSite X).siteTopology.over x).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  sorry

/-- The object property of quasi-coherent module sheaves on `X_spaces,étale`. -/
abbrev spacesQuasiCoherentModuleProperty (X : AlgebraicSpace S) :
    ObjectProperty (RingedSite.ModuleCat.{u} (spacesRingedSite X)) :=
  SheafOfModules.isQuasicoherent (spacesRingedSite X).structureSheaf

/-- `spacesQuasiCoherentModuleProperty X` is mathlib's quasi-coherence predicate on
the structure sheaf of the spaces-étale ringed site. -/
theorem spacesQuasiCoherentModuleProperty_eq (X : AlgebraicSpace S) :
    spacesQuasiCoherentModuleProperty X =
      SheafOfModules.isQuasicoherent (spacesRingedSite X).structureSheaf :=
  sorry

/-- Inverse image `a^*` of modules along the spaces-étale augmentation. -/
abbrev modulePullback :
    RingedSite.ModuleCat.{u} (spacesRingedSite X) ⥤
      RingedSite.ModuleCat.{u} (etaleTotalRingedSite U) :=
  (spacesEtaleAugmentationRinged U a).modulePullback

/-- `modulePullback a` is module pullback along `spacesEtaleAugmentationRinged`. -/
theorem modulePullback_eq :
    modulePullback a = (spacesEtaleAugmentationRinged U a).modulePullback :=
  sorry

/-- Direct image `a_*` of modules along the spaces-étale augmentation. -/
abbrev modulePushforward :
    RingedSite.ModuleCat.{u} (etaleTotalRingedSite U) ⥤
      RingedSite.ModuleCat.{u} (spacesRingedSite X) :=
  (spacesEtaleAugmentationRinged U a).modulePushforward

/-- `modulePushforward a` is module pushforward along `spacesEtaleAugmentationRinged`. -/
theorem modulePushforward_eq :
    modulePushforward a = (spacesEtaleAugmentationRinged U a).modulePushforward :=
  sorry

/-- The adjunction `a^* ⊣ a_*` of modules along the spaces-étale augmentation. -/
abbrev moduleAdjunction : modulePullback a ⊣ modulePushforward a :=
  (spacesEtaleAugmentationRinged U a).moduleAdjunction

/-- `moduleAdjunction a` is the ringed-topos module adjunction of
`spacesEtaleAugmentationRinged`. -/
theorem moduleAdjunction_eq :
    moduleAdjunction a = (spacesEtaleAugmentationRinged U a).moduleAdjunction :=
  sorry

/-- Pullback of modules along the spaces-étale augmentation preserves quasi-coherence. -/
theorem modulePullback_le_inverseImage :
    spacesQuasiCoherentModuleProperty X ≤
      (quasiCoherentModuleProperty U).inverseImage (modulePullback a) :=
  sorry

/-- If `a` is an fppf hypercovering, then pushforward of modules along the spaces-étale
augmentation preserves quasi-coherence. -/
theorem modulePushforward_le_inverseImage (ha : IsFppfHypercovering a) :
    quasiCoherentModuleProperty U ≤
      (spacesQuasiCoherentModuleProperty X).inverseImage (modulePushforward a) :=
  sorry

namespace QCoh

/-- Restriction of `a^*` to quasi-coherent modules. -/
def pullback :
    (spacesQuasiCoherentModuleProperty X).FullSubcategory ⥤ QCoh U :=
  FullSubcategory.restrict (modulePullback a) (modulePullback_le_inverseImage a)

/-- The underlying module sheaf of `QCoh.pullback a` is module pullback along the
spaces-étale augmentation. -/
theorem pullback_obj (F : (spacesQuasiCoherentModuleProperty X).FullSubcategory) :
    ((pullback a).obj F).obj = (modulePullback a).obj F.obj :=
  sorry

/-- Restriction of `a_*` to quasi-coherent modules, when `a` is an fppf hypercovering. -/
def pushforward (ha : IsFppfHypercovering a) :
    QCoh U ⥤ (spacesQuasiCoherentModuleProperty X).FullSubcategory :=
  FullSubcategory.restrict (modulePushforward a) (modulePushforward_le_inverseImage a ha)

/-- The underlying module sheaf of `QCoh.pushforward a ha` is module pushforward along
the spaces-étale augmentation. -/
theorem pushforward_obj (ha : IsFppfHypercovering a) (G : QCoh U) :
    ((pushforward a ha).obj G).obj = (modulePushforward a).obj G.obj :=
  sorry

/-- Inverse image `a^*` on quasi-coherent modules along an fppf hypercovering is full. -/
theorem pullback_full (ha : IsFppfHypercovering a) : (pullback a).Full :=
  sorry

/-- Inverse image `a^*` on quasi-coherent modules along an fppf hypercovering is
faithful. -/
theorem pullback_faithful (ha : IsFppfHypercovering a) : (pullback a).Faithful :=
  sorry

/-- Inverse image `a^*` on quasi-coherent modules along an fppf hypercovering is fully
faithful. -/
def pullback_fullyFaithful (ha : IsFppfHypercovering a) :
    (pullback a).FullyFaithful :=
  @FullyFaithful.ofFullyFaithful _ _ _ _ (pullback a)
    (pullback_full a ha) (pullback_faithful a ha)

end QCoh

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
