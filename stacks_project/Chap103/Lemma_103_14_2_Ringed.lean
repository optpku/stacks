/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.LowerShriek
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import stacks_project.Chap96.Lemma_96_12_4_EtaleModules
public import stacks_project.Chap103.Lemma_103_14_2_Topos

/-!
# Restricted structure sheaves and ringed morphisms of topoi

Restriction of `𝒪_X` along the lisse-étale and flat-fppf inclusions yields the
structure sheaves of the small sites. The resulting morphisms of ringed topoi
have invertible structure maps, so geometric inverse image agrees with module
pullback and is exact.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.Functor CategoryTheory.Limits
open RingedSite.Cocontinuous
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- The structure sheaf `𝒪_{X_lisse,étale}` is the restriction of the étale
structure sheaf along the lisse-étale inclusion. -/
abbrev lisseEtaleStructureSheaf (X : GroupoidsOver S) [AlgebraicStack X] :
    Sheaf (lisseEtaleTopology X) RingCat.{u} :=
  inverseImageRingSheaf (lisseEtaleInclusion X) (etaleStructureSheaf X)

/-- `lisseEtaleStructureSheaf` is continuous pushforward of `etaleStructureSheaf`. -/
theorem lisseEtaleStructureSheaf_eq (X : GroupoidsOver S) [AlgebraicStack X] :
    lisseEtaleStructureSheaf X =
      ((lisseEtaleInclusion X).sheafPushforwardContinuous RingCat.{u}
        (lisseEtaleTopology X) X.etaleTopology).obj (etaleStructureSheaf X) :=
  sorry

/-- The lisse-étale site of `X`, ringed by the restricted structure sheaf. -/
abbrev lisseEtaleRingedSite (X : GroupoidsOver S) [AlgebraicStack X] :
    RingedSite.{u + 1, u, u} :=
  RingedSite.ofRingSheaf (lisseEtaleTopology X) (lisseEtaleStructureSheaf X)

/-- The structure sheaf of `lisseEtaleRingedSite X` is `lisseEtaleStructureSheaf X`. -/
theorem lisseEtaleRingedSite_structureSheaf (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (lisseEtaleRingedSite X).structureSheaf = lisseEtaleStructureSheaf X :=
  sorry

/-- The identity/restriction map of étale structure sheaves as ring presheaves. -/
def lisseEtaleStructurePresheafHom (X : GroupoidsOver S) [AlgebraicStack X] :
    (lisseEtaleInclusion X).op ⋙ (etaleStructureSheaf X).obj ⟶
      (lisseEtaleStructureSheaf X).obj :=
  ((lisseEtaleInclusion X).sheafPushforwardContinuousCompSheafToPresheafIso
      RingCat.{u} (lisseEtaleTopology X) X.etaleTopology).inv.app
    (etaleStructureSheaf X)

/-- `lisseEtaleStructurePresheafHom` is the inverse of the continuous-pushforward
comparison on `etaleStructureSheaf`. -/
theorem lisseEtaleStructurePresheafHom_eq (X : GroupoidsOver S)
    [AlgebraicStack X] :
    lisseEtaleStructurePresheafHom X =
      ((lisseEtaleInclusion X).sheafPushforwardContinuousCompSheafToPresheafIso
          RingCat.{u} (lisseEtaleTopology X) X.etaleTopology).inv.app
        (etaleStructureSheaf X) :=
  sorry

/-- The morphism of ringed topoi induced by the lisse-étale inclusion, with
identity restriction map on structure sheaves. -/
def lisseEtaleRingedToposHom (X : GroupoidsOver S) [AlgebraicStack X] :
    RingedSite.ToposHom (lisseEtaleRingedSite X) (etaleRingedSite X) :=
  @toRingedTopos.{u + 1, u, u + 1, u, u}
    (lisseEtaleRingedSite X) (etaleRingedSite X) (lisseEtaleInclusion X)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (lisseEtaleStructurePresheafHom X)

/-- The underlying morphism of topoi of `lisseEtaleRingedToposHom` is
`lisseEtaleToposHom`. -/
theorem lisseEtaleRingedToposHom_toTopos (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (lisseEtaleRingedToposHom X).toTopos = lisseEtaleToposHom X :=
  sorry

/-- The inverse-image structure map of the lisse-étale ringed morphism is an
isomorphism. -/
instance lisseEtaleRingedToposHom.structureMap_isIso
    (X : GroupoidsOver S) [AlgebraicStack X] :
    IsIso (lisseEtaleRingedToposHom X).structureMap :=
  sorry

/-- Restriction of scalars along the lisse-étale structure map is a right
adjoint. -/
instance lisseEtaleRingedToposHom.restrictScalars_isRightAdjoint
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (SheafOfModules.restrictScalars.{u}
      (lisseEtaleRingedToposHom X).structureMap).IsRightAdjoint :=
  sorry

/-- Module pullback along the lisse-étale ringed morphism factors as geometric
inverse image followed by extension of scalars. -/
theorem lisseEtaleRingedToposHom_modulePullback_eq
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (lisseEtaleRingedToposHom X).modulePullback =
      (lisseEtaleRingedToposHom X).toTopos.moduleInverseImage
          (etaleRingedSite X).structureSheaf ⋙
        SheafOfModules.ChangeOfRings.extendScalars
          (lisseEtaleRingedToposHom X).structureMap :=
  sorry

/-- Module pullback along the lisse-étale ringed morphism preserves finite
limits. -/
instance lisseEtaleRingedToposHom.modulePullback_preservesFiniteLimits
    (X : GroupoidsOver S) [AlgebraicStack X] :
    PreservesFiniteLimits (lisseEtaleRingedToposHom X).modulePullback :=
  sorry

/-- Module pullback along the lisse-étale ringed morphism preserves finite
colimits. -/
instance lisseEtaleRingedToposHom.modulePullback_preservesFiniteColimits
    (X : GroupoidsOver S) [AlgebraicStack X] :
    PreservesFiniteColimits (lisseEtaleRingedToposHom X).modulePullback :=
  sorry

/-- The structure sheaf `𝒪_{X_flat,fppf}` is the restriction of `𝒪_X` along the
flat-fppf inclusion. -/
abbrev flatFppfStructureSheaf (X : GroupoidsOver S) [AlgebraicStack X] :
    Sheaf (flatFppfTopology X) RingCat.{u} :=
  inverseImageRingSheaf (flatFppfInclusion X) (structureSheaf X)

/-- `flatFppfStructureSheaf` is continuous pushforward of `structureSheaf`. -/
theorem flatFppfStructureSheaf_eq (X : GroupoidsOver S) [AlgebraicStack X] :
    flatFppfStructureSheaf X =
      ((flatFppfInclusion X).sheafPushforwardContinuous RingCat.{u}
        (flatFppfTopology X) (inheritedFppfTopology X)).obj (structureSheaf X) :=
  sorry

/-- The flat-fppf site of `X`, ringed by the restricted structure sheaf. -/
abbrev flatFppfRingedSite (X : GroupoidsOver S) [AlgebraicStack X] :
    RingedSite.{u + 1, u, u} :=
  RingedSite.ofRingSheaf (flatFppfTopology X) (flatFppfStructureSheaf X)

/-- The structure sheaf of `flatFppfRingedSite X` is `flatFppfStructureSheaf X`. -/
theorem flatFppfRingedSite_structureSheaf (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (flatFppfRingedSite X).structureSheaf = flatFppfStructureSheaf X :=
  sorry

/-- The identity/restriction map of fppf structure sheaves as ring presheaves. -/
def flatFppfStructurePresheafHom (X : GroupoidsOver S) [AlgebraicStack X] :
    (flatFppfInclusion X).op ⋙ (structureSheaf X).obj ⟶
      (flatFppfStructureSheaf X).obj :=
  ((flatFppfInclusion X).sheafPushforwardContinuousCompSheafToPresheafIso
      RingCat.{u} (flatFppfTopology X) (inheritedFppfTopology X)).inv.app
    (structureSheaf X)

/-- `flatFppfStructurePresheafHom` is the inverse of the continuous-pushforward
comparison on `structureSheaf`. -/
theorem flatFppfStructurePresheafHom_eq (X : GroupoidsOver S)
    [AlgebraicStack X] :
    flatFppfStructurePresheafHom X =
      ((flatFppfInclusion X).sheafPushforwardContinuousCompSheafToPresheafIso
          RingCat.{u} (flatFppfTopology X) (inheritedFppfTopology X)).inv.app
        (structureSheaf X) :=
  sorry

/-- The morphism of ringed topoi induced by the flat-fppf inclusion, with
identity restriction map on structure sheaves. -/
def flatFppfRingedToposHom (X : GroupoidsOver S) [AlgebraicStack X] :
    RingedSite.ToposHom (flatFppfRingedSite X) (ringedSite X) :=
  @toRingedTopos.{u + 1, u, u + 1, u, u}
    (flatFppfRingedSite X) (ringedSite X) (flatFppfInclusion X)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (flatFppfStructurePresheafHom X)

/-- The underlying morphism of topoi of `flatFppfRingedToposHom` is
`flatFppfToposHom`. -/
theorem flatFppfRingedToposHom_toTopos (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (flatFppfRingedToposHom X).toTopos = flatFppfToposHom X :=
  sorry

/-- The inverse-image structure map of the flat-fppf ringed morphism is an
isomorphism. -/
instance flatFppfRingedToposHom.structureMap_isIso
    (X : GroupoidsOver S) [AlgebraicStack X] :
    IsIso (flatFppfRingedToposHom X).structureMap :=
  sorry

/-- Restriction of scalars along the flat-fppf structure map is a right
adjoint. -/
instance flatFppfRingedToposHom.restrictScalars_isRightAdjoint
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (SheafOfModules.restrictScalars.{u}
      (flatFppfRingedToposHom X).structureMap).IsRightAdjoint :=
  sorry

/-- Module pullback along the flat-fppf ringed morphism factors as geometric
inverse image followed by extension of scalars. -/
theorem flatFppfRingedToposHom_modulePullback_eq
    (X : GroupoidsOver S) [AlgebraicStack X] :
    (flatFppfRingedToposHom X).modulePullback =
      (flatFppfRingedToposHom X).toTopos.moduleInverseImage
          (ringedSite X).structureSheaf ⋙
        SheafOfModules.ChangeOfRings.extendScalars
          (flatFppfRingedToposHom X).structureMap :=
  sorry

/-- Module pullback along the flat-fppf ringed morphism preserves finite
limits. -/
instance flatFppfRingedToposHom.modulePullback_preservesFiniteLimits
    (X : GroupoidsOver S) [AlgebraicStack X] :
    PreservesFiniteLimits (flatFppfRingedToposHom X).modulePullback :=
  sorry

/-- Module pullback along the flat-fppf ringed morphism preserves finite
colimits. -/
instance flatFppfRingedToposHom.modulePullback_preservesFiniteColimits
    (X : GroupoidsOver S) [AlgebraicStack X] :
    PreservesFiniteColimits (flatFppfRingedToposHom X).modulePullback :=
  sorry

end AlgebraicGeometry.AlgebraicStack
