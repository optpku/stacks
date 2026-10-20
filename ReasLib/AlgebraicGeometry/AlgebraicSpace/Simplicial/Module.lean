module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.RingedComparison

/-! # Module functors of a spaces-étale augmentation -/

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

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
