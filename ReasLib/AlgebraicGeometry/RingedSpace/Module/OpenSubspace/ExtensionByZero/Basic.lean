/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.OpenSubsetExtensionByInitial
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous.Restrict
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Restriction
public import ReasLib.Topology.Sheaves.Ring.Pullback
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Extension by zero for modules on open subspaces

This file owns the underived lower-shriek functor for an open subspace of a ringed space.  It
separates the generic module-sheaf extension-by-zero construction from the change-of-rings
comparison which identifies the restricted ringed-space structure sheaf with the ambient pullback.
-/

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The category of module sheaves over the pullback of `X`'s ring sheaf to the open subspace
`U`.  This is the ambient-pullback model for modules on `X|_U`. -/
abbrev pullbackModuleCategory
    (X : RingedSpace.{u}) (U : Opens X.carrier) :=
  SheafOfModules
    ((TopCat.Sheaf.pullback RingCat U.inclusion').obj (RingedSpace.ringCatSheaf X))

/-- The canonical identification of the structure ring sheaf on `X|_U` with the pullback of the
structure ring sheaf on `X`. -/
noncomputable abbrev openSubspaceRingSheafIso
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    RingedSpace.ringCatSheaf (X.restrict U.isOpenEmbedding) ≅
      (TopCat.Sheaf.pullback RingCat U.inclusion').obj (RingedSpace.ringCatSheaf X) := by
  let eComm :
      (X.restrict U.isOpenEmbedding).sheaf ≅
        (TopCat.Sheaf.pullback CommRingCat U.inclusion').obj X.sheaf :=
    (U.isOpenEmbedding.sheafPullbackIso CommRingCat).symm.app X.sheaf
  -- Defeq pin between the opens-site presentation of `X.restrict U` and `TopCat.of U`.
  let _ :
      (Opens.grothendieckTopology
        ↑((Opens.toTopCat ↑X.toPresheafedSpace).obj U)).PreservesSheafification
        (forget₂ CommRingCat RingCat.{u}) := by
    change (Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})
    infer_instance
  change
    (sheafCompose (Opens.grothendieckTopology (TopCat.of U))
      (forget₂ CommRingCat RingCat)).obj
        ((X.restrict U.isOpenEmbedding).sheaf) ≅
      (TopCat.Sheaf.pullback RingCat U.inclusion').obj (RingedSpace.ringCatSheaf X)
  exact
    (sheafCompose (Opens.grothendieckTopology (TopCat.of U))
      (forget₂ CommRingCat RingCat)).mapIso eComm ≪≫
      TopCat.Sheaf.ringSheafOfCommPullbackIso U.inclusion' X.sheaf

/-- The change-of-rings bridge from intrinsic `𝒪_U`-modules to modules over the pullback model
of the ambient structure sheaf. -/
noncomputable abbrev OpenSubspace.restrictionAlongRingSheafIso
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    openSubspaceModuleCategory X U ⥤ pullbackModuleCategory X U :=
  SheafOfModules.restrictScalars (openSubspaceRingSheafIso X U).inv

namespace OpenSubspace

/-- The canonical equivalence between intrinsic modules on `X|_U` and modules over the pullback
of the ambient structure sheaf to `U`. -/
noncomputable def moduleEquivalence
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    openSubspaceModuleCategory X U ≌ pullbackModuleCategory X U :=
  SheafOfModules.Restriction.equivalenceOfIso (openSubspaceRingSheafIso X U)

/-- The open-subspace pullback unit followed by the inverse structure-sheaf comparison is the
structure-sheaf map of the open immersion `X|_U ⟶ X`. -/
theorem pullbackUnit_comp_ringSheafIso_inv
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat U.inclusion').unit.app
          X.ringCatSheaf ≫
        (TopCat.Sheaf.pushforward RingCat U.inclusion').map
          (openSubspaceRingSheafIso X U).inv =
      RingedSpace.Hom.toRingCatSheafHom (X.ofRestrict U.isOpenEmbedding) := sorry

/-- Restriction to the intrinsic open subspace is the generic open-subset restriction followed
by the inverse of `moduleEquivalence`. -/
noncomputable def restrictionIso
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    SheafOfModules.OpenSubset.Restriction.functor U X.ringCatSheaf ⋙
        (moduleEquivalence X U).inverse ≅
      moduleRestrictionToOpen X U :=
  (SheafOfModules.pullbackIsoOfIso
    ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat U.inclusion').unit.app
      X.ringCatSheaf)
    (RingedSpace.Hom.toRingCatSheafHom (X.ofRestrict U.isOpenEmbedding))
    (openSubspaceRingSheafIso X U).symm
    (pullbackUnit_comp_ringSheafIso_inv X U)).symm

end OpenSubspace

/-- The change-of-rings bridge for an open subspace is additive. -/
private instance restrictionAlongRingSheafIso_additive
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    (OpenSubspace.restrictionAlongRingSheafIso X U).Additive := sorry

/-- The change-of-rings bridge for an open subspace preserves finite limits. -/
private instance restrictionAlongRingSheafIso_preservesFiniteLimits
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    PreservesFiniteLimits (OpenSubspace.restrictionAlongRingSheafIso X U) := sorry

/-- The change-of-rings bridge for an open subspace preserves finite colimits. -/
private instance restrictionAlongRingSheafIso_preservesFiniteColimits
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    PreservesFiniteColimits (OpenSubspace.restrictionAlongRingSheafIso X U) := sorry

/-- Extension by zero from the ambient-pullback model of module sheaves on `U` to module sheaves
on `X`. -/
abbrev pulledBackModuleSheafExtensionByZeroFromOpen
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    pullbackModuleCategory X U ⥤ RingedSpace.Modules X :=
  SheafOfModules.OpenSubset.ExtensionByZero.functor U (RingedSpace.ringCatSheaf X)

/-- Generic module-sheaf extension by zero is additive in the ambient pullback model. -/
private instance pulledBackModuleSheafExtensionByZeroFromOpen_additive
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (pulledBackModuleSheafExtensionByZeroFromOpen X U).Additive := sorry

/-- Generic module-sheaf extension by zero preserves finite limits in the ambient pullback
model. -/
private instance pulledBackModuleSheafExtensionByZeroFromOpen_preservesFiniteLimits
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    PreservesFiniteLimits (pulledBackModuleSheafExtensionByZeroFromOpen X U) := sorry

/-- Generic module-sheaf extension by zero preserves finite colimits in the ambient pullback
model. -/
private instance pulledBackModuleSheafExtensionByZeroFromOpen_preservesFiniteColimits
    (X : RingedSpace.{u}) (U : Opens X.carrier) :
    PreservesFiniteColimits (pulledBackModuleSheafExtensionByZeroFromOpen X U) := sorry

/-- The intrinsic extension-by-zero functor `j_! : Mod(𝒪_U) ⥤ Mod(𝒪_X)` for the open immersion
`j : U ↪ X`. -/
@[stacks 00A4 "sheaf of modules extension by zero"]
noncomputable abbrev moduleExtensionByZeroFromOpen
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    openSubspaceModuleCategory X U ⥤ RingedSpace.Modules X :=
  OpenSubspace.restrictionAlongRingSheafIso X U ⋙
    pulledBackModuleSheafExtensionByZeroFromOpen X U

/-- Extension by zero from an open subspace is additive. -/
instance OpenSubspace.ExtensionByZero.additive
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    (moduleExtensionByZeroFromOpen X U).Additive := sorry

/-- Extension by zero from an open subspace preserves finite limits. -/
@[stacks 01AK "module lower shriek preserves finite limits"]
instance OpenSubspace.ExtensionByZero.preservesFiniteLimits
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    PreservesFiniteLimits (moduleExtensionByZeroFromOpen X U) := sorry

/-- Extension by zero from an open subspace preserves finite colimits. -/
@[stacks 01AK "module lower shriek preserves finite colimits"]
instance OpenSubspace.ExtensionByZero.preservesFiniteColimits
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    PreservesFiniteColimits (moduleExtensionByZeroFromOpen X U) := sorry

/-- The intrinsic extension-by-zero functor on `𝒪_U`-modules is left adjoint to restriction to
the open subspace `U`. -/
@[stacks 00A5 "sheaf of modules extension-restriction adjunction"]
noncomputable def OpenSubspace.ExtensionByZero.adjunction
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    moduleExtensionByZeroFromOpen X U ⊣ moduleRestrictionToOpen X U :=
  (((OpenSubspace.moduleEquivalence X U).toAdjunction.comp
      (SheafOfModules.OpenSubset.ExtensionByZero.adjunction U X.ringCatSheaf)).ofNatIsoRight
    (OpenSubspace.restrictionIso X U))

namespace OpenSubspace.ExtensionByZero

/-- The unit of intrinsic extension by zero followed by restriction is an isomorphism. -/
instance unitIsIso
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    IsIso (adjunction X U).unit := sorry

/-- Every component of the extension-restriction unit is an isomorphism. -/
@[stacks 00A5 "module extension-restriction unit component"]
instance unitAppIsIso
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})]
    (F : openSubspaceModuleCategory X U) :
    IsIso ((adjunction X U).unit.app F) := sorry

/-- Intrinsic extension by zero from an open subspace is fully faithful. -/
@[stacks 00A5 "intrinsic module extension by zero is fully faithful"]
noncomputable def fullyFaithful
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    (moduleExtensionByZeroFromOpen X U).FullyFaithful :=
  (OpenSubspace.moduleEquivalence X U).fullyFaithfulFunctor.comp
    (SheafOfModules.OpenSubset.ExtensionByZero.fullyFaithful U X.ringCatSheaf)

/-- Intrinsic extension by zero from an open subspace is full. -/
noncomputable instance full
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    (moduleExtensionByZeroFromOpen X U).Full :=
  (fullyFaithful X U).full

/-- Intrinsic extension by zero from an open subspace is faithful. -/
noncomputable instance faithful
    (X : RingedSpace.{u}) (U : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})] :
    (moduleExtensionByZeroFromOpen X U).Faithful :=
  (fullyFaithful X U).faithful

end OpenSubspace.ExtensionByZero

end AlgebraicGeometry.RingedSpace
