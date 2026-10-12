/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Subset
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous.Restrict
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.Topology.Sheaves.Ring.Pullback
public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Module sheaves on closed subsets of ringed spaces

This file provides the fundamental infrastructure for working with `𝒪_X|_Z`-modules on
a closed subset `Z ⊆ X` of a ringed space:

- `ClosedSubset.inclusion`: the inclusion `Z ↪ X`
- `ClosedSubset.ringCatSheaf`: the restricted structure sheaf `𝒪_X|_Z`
- `ClosedSubset.Modules`: the category of `𝒪_X|_Z`-modules
- `ClosedSubset.pullback`: restriction from `X.Modules` to `Z`-modules
- `ClosedSubset.pushforward`: extension from `Z`-modules to `X.Modules`
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {Z : Set X}

namespace ClosedSubset

/-- The ringed subspace carried by a bundled closed subset, with structure sheaf obtained by
pulling back the ambient commutative-ring sheaf. -/
@[stacks 0G75 "ringed subspace on a closed subset"]
noncomputable def ringedSpace (X : RingedSpace.{u}) (Z : Closeds X) : RingedSpace.{u} :=
  ((TopCat.Sheaf.pullback CommRingCat.{u} (TopCat.subsetInclusion Z)).obj X.sheaf).toRingedSpace

/-- The canonical morphism from the ringed subspace on a closed subset to its ambient ringed
space. -/
@[stacks 0G75 "closed-subset inclusion of ringed spaces"]
noncomputable def inclusionHom (X : RingedSpace.{u}) (Z : Closeds X) :
    ringedSpace X Z ⟶ X :=
  ⟨⟨TopCat.subsetInclusion (Z : Set X),
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      (TopCat.subsetInclusion (Z : Set X))).unit.app X.sheaf |>.hom⟩⟩

/-- The underlying map of the canonical closed-subspace inclusion is a closed embedding. -/
@[stacks 0G78 "closed embedding of the bundled closed-subspace inclusion"]
theorem inclusionHom_isClosedEmbedding (X : RingedSpace.{u}) (Z : Closeds X) :
    Topology.IsClosedEmbedding (inclusionHom X Z).hom.base := sorry

/-- The inverse image of a bundled closed subset under a morphism of ringed spaces. -/
@[stacks 0G78 "inverse image of a closed subset"]
abbrev preimage {X Y : RingedSpace.{u}} (f : X ⟶ Y) (Z : Closeds Y) : Closeds X :=
  Z.preimage f.hom.base.hom.continuous

/-- The continuous map between closed subspaces induced by a morphism of ringed spaces. -/
@[stacks 0G78 "map on inverse-image closed subspaces"]
def restrictedBase {X Y : RingedSpace.{u}} (f : X ⟶ Y) (Z : Closeds Y) :
    TopCat.subsetSpace (preimage f Z : Set X) ⟶ TopCat.subsetSpace (Z : Set Y) :=
  TopCat.ofHom
    ⟨Subtype.map f.hom.base.hom fun _ h ↦ h,
      f.hom.base.hom.continuous.subtype_map fun _ h ↦ h⟩

/-- The inverse-image structure-sheaf map defining the restriction of a ringed-space morphism
to an inverse-image closed subset. -/
@[stacks 0G78 "structure map on inverse-image closed subspaces"]
noncomputable def restrictedPullbackMap {X Y : RingedSpace.{u}}
    (f : X ⟶ Y) (Z : Closeds Y) :
    (TopCat.Sheaf.pullback CommRingCat.{u} (restrictedBase f Z)).obj
        (ringedSpace Y Z).sheaf ⟶
      (ringedSpace X (preimage f Z)).sheaf :=
  (TopCat.Sheaf.pullbackComp (A := CommRingCat.{u})
      (restrictedBase f Z) (TopCat.subsetInclusion (Z : Set Y))).hom.app Y.sheaf ≫
    (TopCat.Sheaf.pullbackCongr (A := CommRingCat.{u})
      rfl).hom.app Y.sheaf ≫
    (TopCat.Sheaf.pullbackComp (A := CommRingCat.{u})
      (TopCat.subsetInclusion (preimage f Z : Set X)) f.hom.base).inv.app Y.sheaf ≫
    (TopCat.Sheaf.pullback CommRingCat.{u}
      (TopCat.subsetInclusion (preimage f Z : Set X))).map
        (RingedSpace.Hom.inverseImageStructureSheafHomComm f)

/-- The morphism between closed ringed subspaces induced by a morphism of ambient ringed
spaces. Its source is indexed by the canonical inverse-image closed subset. -/
@[stacks 0G78 "morphism on inverse-image closed subspaces"]
noncomputable def restrictedHom {X Y : RingedSpace.{u}}
    (f : X ⟶ Y) (Z : Closeds Y) :
    ringedSpace X (preimage f Z) ⟶ ringedSpace Y Z :=
  ⟨⟨restrictedBase f Z,
    (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      (restrictedBase f Z)).homEquiv _ _)
        (restrictedPullbackMap f Z)).hom⟩⟩

/-- Restricting a ringed-space morphism to an inverse-image closed subset commutes with the
canonical closed-subspace inclusions. -/
@[stacks 0G78 "factorization through inverse-image closed subspaces"]
theorem restrictedHom_fac {X Y : RingedSpace.{u}}
    (f : X ⟶ Y) (Z : Closeds Y) :
    restrictedHom f Z ≫ inclusionHom Y Z =
      inclusionHom X (preimage f Z) ≫ f := sorry

/-- The inclusion of a closed subset into the ambient ringed space. -/
abbrev inclusion (X : RingedSpace.{u}) (Z : Set X) : TopCat.of Z ⟶ X :=
  SheafOfModules.Subset.inclusion Z

/-- The restricted structure sheaf `𝒪_X|_Z` on a closed subset. -/
abbrev ringCatSheaf (X : RingedSpace.{u}) (Z : Set X) :
    TopCat.Sheaf RingCat.{u} (TopCat.of Z) :=
  SheafOfModules.Subset.ringSheaf X.ringCatSheaf Z

/-- The category of `𝒪_X|_Z`-modules on a closed subset. -/
abbrev Modules (X : RingedSpace.{u}) (Z : Set X) :=
  SheafOfModules.Subset.Modules X.ringCatSheaf Z

/-- The underlying ring sheaf of the intrinsic closed ringed subspace is canonically the
RingCat-valued pullback used by the legacy closed-subset module model. -/
@[stacks 0G75 "comparison of closed-subspace structure sheaves"]
noncomputable abbrev ringCatSheafIso (X : RingedSpace.{u}) (Z : Closeds X)
    [(Opens.grothendieckTopology (TopCat.of Z)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    (ringedSpace X Z).ringCatSheaf ≅ ringCatSheaf X Z :=
  TopCat.Sheaf.ringSheafOfCommPullbackIso
    (TopCat.subsetInclusion (Z : Set X)) X.sheaf

/-- The canonical equivalence from intrinsic modules on a closed ringed subspace to the
RingCat-pullback presentation used by `ClosedSubset.Modules`. -/
@[stacks 0G75 "comparison of closed-subspace module categories"]
noncomputable def moduleEquivalence (X : RingedSpace.{u}) (Z : Closeds X)
    [(Opens.grothendieckTopology (TopCat.of Z)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    (ringedSpace X Z).Modules ≌ Modules X Z :=
  SheafOfModules.Restriction.equivalenceOfIso (ringCatSheafIso X Z)

/-- The canonical structure-sheaf map `𝒪_X → i_* 𝒪_X|_Z`. -/
abbrev structureSheafHom (X : RingedSpace.{u}) (Z : Set X) :
    X.ringCatSheaf ⟶
      (TopCat.Sheaf.pushforward RingCat.{u}
        (inclusion X Z)).obj (ringCatSheaf X Z) :=
  SheafOfModules.Subset.structureSheafHom X.ringCatSheaf Z

/-- Restriction of `𝒪_X`-modules to a closed subset. -/
abbrev pullback (X : RingedSpace.{u}) (Z : Set X) :
    X.Modules ⥤ Modules X Z :=
  SheafOfModules.Subset.pullback X.ringCatSheaf Z

/-- Pushforward of `𝒪_X|_Z`-modules back to `X`. -/
noncomputable abbrev pushforward (X : RingedSpace.{u}) (Z : Set X) :
    Modules X Z ⥤ X.Modules :=
  SheafOfModules.Subset.pushforward X.ringCatSheaf Z

/-- Pushforward of closed-subset modules is additive. -/
noncomputable instance pushforward_additive (X : RingedSpace.{u}) (Z : Set X) :
    (pushforward X Z).Additive := inferInstance

namespace Inclusion

variable (X : RingedSpace.{u}) (Z : Closeds X)
variable [(Opens.grothendieckTopology (TopCat.of Z)).PreservesSheafification
  (forget₂ CommRingCat RingCat.{u})]

/-- Forgetting commutativity in the intrinsic structure map and then identifying the restricted
structure sheaf gives the legacy closed-subset structure map. -/
@[stacks 0G75 "compatibility of the closed-subset structure map"]
theorem structureMap_hom :
    RingedSpace.Hom.toRingCatSheafHom (inclusionHom X Z) ≫
        (TopCat.Sheaf.pushforward RingCat.{u} (inclusion X Z)).map
          (ringCatSheafIso X Z).hom =
      structureSheafHom X Z := sorry

/-- Intrinsic pullback to a closed ringed subspace agrees with restriction to the underlying
closed subset after the canonical change of rings. -/
@[stacks 0G75 "comparison of pullback to a closed subspace"]
noncomputable def pullbackIso :
    RingedSpace.Hom.pullback (inclusionHom X Z) ⋙
        (moduleEquivalence X Z).functor ≅
      pullback X Z :=
  (SheafOfModules.pullbackIsoOfIso
    (RingedSpace.Hom.toRingCatSheafHom (inclusionHom X Z))
    (structureSheafHom X Z) (ringCatSheafIso X Z)
    (structureMap_hom X Z)).symm

/-- Intrinsic pushforward from a closed ringed subspace agrees with the legacy closed-subset
pushforward after the canonical change of rings. -/
@[stacks 0G75 "comparison of pushforward from a closed subspace"]
noncomputable def pushforwardIso :
    (moduleEquivalence X Z).functor ⋙ pushforward X Z ≅
      RingedSpace.Hom.pushforward (inclusionHom X Z) :=
  (Iso.isoInverseComp (G := (moduleEquivalence X Z).symm)
    (SheafOfModules.restrictPushforwardIso (ringCatSheafIso X Z).hom
      (RingedSpace.Hom.toRingCatSheafHom (inclusionHom X Z))
      (structureSheafHom X Z) (structureMap_hom X Z))).symm

end Inclusion

end ClosedSubset

end AlgebraicGeometry.RingedSpace
