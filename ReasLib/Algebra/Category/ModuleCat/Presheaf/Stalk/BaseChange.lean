/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Stalk.Skyscraper
import Mathlib.Tactic.CrossRefAttribute

/-!
# Scalar extension and stalks of module presheaves

This file owns the comparison between the stalk of `PresheafOfModules.pullback` and extension of
scalars on the stalk.  The pullback functor itself remains the mathlib owner.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Presheaf Opposite TopCat TopologicalSpace
open scoped ChangeOfRings

noncomputable section

universe u

namespace TopCat.Presheaf

/- At the presheaf level, `PresheafOfModules.pullback` is extension of scalars; at the stalk
level, `ModuleCat.extendScalars` is tensor product. The comparison morphism below identifies
these two constructions. -/

/-- The underlying stalk map induced by a morphism to a restricted-scalars presheaf module. -/
noncomputable abbrev stalkUnderlyingMapToRestricted
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    {ℱ : PresheafOfModules (ringPresheafOfComm 𝒪)}
    {𝒢 : PresheafOfModules (ringPresheafOfComm 𝒪')}
    (φ : ℱ ⟶
      (PresheafOfModules.restrictScalars
        (commRingPresheafHomOverId p)).obj 𝒢) (x : X) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ℱ.presheaf x →
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) 𝒢.presheaf x :=
  (stalkFunctor Ab x).map
    ((PresheafOfModules.toPresheaf (ringPresheafOfComm 𝒪)).map φ)

/-- The stalk map to a restricted-scalars target preserves addition. -/
theorem stalkUnderlyingMapToRestricted_map_add
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    {ℱ : PresheafOfModules (ringPresheafOfComm 𝒪)}
    {𝒢 : PresheafOfModules (ringPresheafOfComm 𝒪')}
    (φ : ℱ ⟶
      (PresheafOfModules.restrictScalars
        (commRingPresheafHomOverId p)).obj 𝒢) (x : X) :
    ∀ m n : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ℱ.presheaf x,
      stalkUnderlyingMapToRestricted p φ x (m + n) =
        stalkUnderlyingMapToRestricted p φ x m +
          stalkUnderlyingMapToRestricted p φ x n := sorry
/- Proof strategy: unfold `stalkUnderlyingMapToRestricted` and use that
`(stalkFunctor Ab x).map` is a morphism in `AddCommGrpCat`; its underlying additive homomorphism
preserves addition by `map_add`. -/

/-- The stalk map to a restricted-scalars target is linear over the induced map on stalk rings. -/
theorem stalkUnderlyingMapToRestricted_map_smul
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    {ℱ : PresheafOfModules (ringPresheafOfComm 𝒪)}
    {𝒢 : PresheafOfModules (ringPresheafOfComm 𝒪')}
    (φ : ℱ ⟶
      (PresheafOfModules.restrictScalars
        (commRingPresheafHomOverId p)).obj 𝒢) (x : X) :
    ∀ (r : 𝒪.stalk x)
      (m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ℱ.presheaf x),
      stalkUnderlyingMapToRestricted p φ x (r • m) =
        ((· • ·) : 𝒪'.stalk x →
          TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) 𝒢.presheaf x →
          TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) 𝒢.presheaf x)
          (((stalkFunctor CommRingCat x).map p) r)
          (stalkUnderlyingMapToRestricted p φ x m) := sorry
/- Proof strategy: represent `r` and `m` by germs on a common neighborhood using
`TopCat.Presheaf.exists_germ_eq`, apply the sectionwise linearity of `φ.app`, and finish with
`PresheafOfModules.germ_smul` and naturality of the stalk functor along `p`. -/

/-- The stalk-linear map into a restricted-scalars target induced by a morphism of presheaf
modules. -/
noncomputable def stalkModuleMapToRestrict
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    {ℱ : PresheafOfModules (ringPresheafOfComm 𝒪)}
    {𝒢 : PresheafOfModules (ringPresheafOfComm 𝒪')}
    (φ : ℱ ⟶
      (PresheafOfModules.restrictScalars
        (commRingPresheafHomOverId p)).obj 𝒢) (x : X) :
    ModuleCat.of (𝒪.stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ℱ.presheaf x) ⟶
      (ModuleCat.restrictScalars (((stalkFunctor CommRingCat x).map p).hom)).obj
        (ModuleCat.of (𝒪'.stalk x)
          (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) 𝒢.presheaf x)) :=
  ConcreteCategory.ofHom
    { toFun := stalkUnderlyingMapToRestricted p φ x
      map_add' := stalkUnderlyingMapToRestricted_map_add p φ x
      map_smul' := stalkUnderlyingMapToRestricted_map_smul p φ x }

/-- The canonical comparison from the extended-scalar stalk `ℱ_x ⊗[𝒪_x] 𝒪'_x` to the stalk of
the canonically extended presheaf. -/
@[stacks 03CU "stalk base-change comparison"]
noncomputable def stalkBaseChangeComparison
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (ringPresheafOfComm 𝒪)) (x : X) :
    (ModuleCat.extendScalars (((stalkFunctor CommRingCat x).map p).hom)).obj
      (ModuleCat.of (𝒪.stalk x)
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ℱ.presheaf x)) ⟶
        ModuleCat.of (𝒪'.stalk x)
          (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
            ((PresheafOfModules.pullback
              (commRingPresheafHomOverId p)).obj ℱ).presheaf x) :=
  ((ModuleCat.extendRestrictScalarsAdj (((stalkFunctor CommRingCat x).map p).hom)).homEquiv
      _ _).symm
    (stalkModuleMapToRestrict p
      ((PresheafOfModules.pullbackPushforwardAdjunction
        (commRingPresheafHomOverId p)).unit.app ℱ) x)

/-- The stalk base-change comparison sends `1 ⊗ₜ m` to the stalk of the extension adjunction
unit applied to `m`. -/
@[stacks 03CU "stalk base-change comparison on generators"]
theorem stalkBaseChangeComparison_one_tmul
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (ringPresheafOfComm 𝒪)) (x : X)
    (m : PresheafOfModules.stalkModuleCatOfCommRing ℱ x) :
    stalkBaseChangeComparison p ℱ x
        ((1 : 𝒪'.stalk x) ⊗ₜ[𝒪.stalk x,
          ((stalkFunctor CommRingCat x).map p).hom] m) =
      stalkUnderlyingMapToRestricted p
        ((PresheafOfModules.pullbackPushforwardAdjunction
          (commRingPresheafHomOverId p)).unit.app ℱ) x m := sorry

/-- The explicit inverse to the stalk base-change comparison.  It is obtained by transporting
the extension-of-scalars unit through the stalk-skyscraper and extension-restriction Hom
equivalences. -/
@[stacks 03CU "inverse stalk base-change comparison"]
noncomputable def stalkBaseChangeComparisonInv
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (ringPresheafOfComm 𝒪)) (x : X) :
    ModuleCat.of (𝒪'.stalk x)
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
          ((PresheafOfModules.pullback
            (commRingPresheafHomOverId p)).obj ℱ).presheaf x) ⟶
      (ModuleCat.extendScalars
        (((stalkFunctor CommRingCat x).map p).hom)).obj
        (ModuleCat.of (𝒪.stalk x)
          (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ℱ.presheaf x)) :=
  (PresheafOfModules.Skyscraper.homEquiv 𝒪' x
    ((PresheafOfModules.pullback
      (commRingPresheafHomOverId p)).obj ℱ)
    ((ModuleCat.extendScalars
      (((stalkFunctor CommRingCat x).map p).hom)).obj
      (PresheafOfModules.stalkModuleCatOfCommRing ℱ x))).symm
    (((PresheafOfModules.ChangeOfRings.extensionRestrictionAdjunction
      (ringPresheafOfCommMap p)).homEquiv ℱ
      (PresheafOfModules.Skyscraper.atPoint 𝒪' x
        ((ModuleCat.extendScalars
          (((stalkFunctor CommRingCat x).map p).hom)).obj
          (PresheafOfModules.stalkModuleCatOfCommRing ℱ x)))).symm
      (PresheafOfModules.Skyscraper.homEquiv 𝒪 x ℱ
        ((ModuleCat.restrictScalars
          (((stalkFunctor CommRingCat x).map p).hom)).obj
          ((ModuleCat.extendScalars
            (((stalkFunctor CommRingCat x).map p).hom)).obj
            (PresheafOfModules.stalkModuleCatOfCommRing ℱ x)))
        ((ModuleCat.extendRestrictScalarsAdj
          (((stalkFunctor CommRingCat x).map p).hom)).unit.app
          (PresheafOfModules.stalkModuleCatOfCommRing ℱ x)) ≫
        (PresheafOfModules.Skyscraper.RestrictScalars.objIso p x
          ((ModuleCat.extendScalars
            (((stalkFunctor CommRingCat x).map p).hom)).obj
            (PresheafOfModules.stalkModuleCatOfCommRing ℱ x))).inv))

/-- Under the stalk-skyscraper equivalence, the inverse stalk base-change map is the
extension-restriction transpose of the scalar-restricted skyscraper map. -/
theorem stalkBaseChangeComparisonInv_adjunct
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (ringPresheafOfComm 𝒪)) (x : X) :
    PresheafOfModules.Skyscraper.homEquiv 𝒪' x
        ((PresheafOfModules.pullback
          (commRingPresheafHomOverId p)).obj ℱ)
        ((ModuleCat.extendScalars
          (((stalkFunctor CommRingCat x).map p).hom)).obj
          (PresheafOfModules.stalkModuleCatOfCommRing ℱ x))
        (stalkBaseChangeComparisonInv p ℱ x) =
      ((PresheafOfModules.ChangeOfRings.extensionRestrictionAdjunction
        (ringPresheafOfCommMap p)).homEquiv ℱ
        (PresheafOfModules.Skyscraper.atPoint 𝒪' x
          ((ModuleCat.extendScalars
            (((stalkFunctor CommRingCat x).map p).hom)).obj
            (PresheafOfModules.stalkModuleCatOfCommRing ℱ x)))).symm
        (PresheafOfModules.Skyscraper.homEquiv 𝒪 x ℱ
          ((ModuleCat.restrictScalars
            (((stalkFunctor CommRingCat x).map p).hom)).obj
            ((ModuleCat.extendScalars
              (((stalkFunctor CommRingCat x).map p).hom)).obj
              (PresheafOfModules.stalkModuleCatOfCommRing ℱ x)))
          ((ModuleCat.extendRestrictScalarsAdj
            (((stalkFunctor CommRingCat x).map p).hom)).unit.app
            (PresheafOfModules.stalkModuleCatOfCommRing ℱ x)) ≫
          (PresheafOfModules.Skyscraper.RestrictScalars.objIso p x
            ((ModuleCat.extendScalars
              (((stalkFunctor CommRingCat x).map p).hom)).obj
              (PresheafOfModules.stalkModuleCatOfCommRing ℱ x))).inv) := sorry

/-- The stalk base-change comparison followed by its explicit inverse is the identity. -/
theorem stalkBaseChangeComparison_hom_inv_id
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (ringPresheafOfComm 𝒪)) (x : X) :
    stalkBaseChangeComparison p ℱ x ≫ stalkBaseChangeComparisonInv p ℱ x = 𝟙 _ := sorry

/-- The explicit inverse followed by the stalk base-change comparison is the identity. -/
theorem stalkBaseChangeComparison_inv_hom_id
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (ringPresheafOfComm 𝒪)) (x : X) :
    stalkBaseChangeComparisonInv p ℱ x ≫ stalkBaseChangeComparison p ℱ x = 𝟙 _ := sorry

/-- Extension of scalars on stalks is canonically isomorphic to the stalk of extension of
scalars of module presheaves. -/
@[stacks 03CU "stalk base-change isomorphism"]
noncomputable def stalkBaseChangeComparisonIso
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (ringPresheafOfComm 𝒪)) (x : X) :
    (ModuleCat.extendScalars (((stalkFunctor CommRingCat x).map p).hom)).obj
        (ModuleCat.of (𝒪.stalk x)
          (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) ℱ.presheaf x)) ≅
      ModuleCat.of (𝒪'.stalk x)
        (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
          ((PresheafOfModules.pullback
            (commRingPresheafHomOverId p)).obj ℱ).presheaf x) where
  hom := stalkBaseChangeComparison p ℱ x
  inv := stalkBaseChangeComparisonInv p ℱ x
  hom_inv_id := stalkBaseChangeComparison_hom_inv_id p ℱ x
  inv_hom_id := stalkBaseChangeComparison_inv_hom_id p ℱ x

/-- The forward map of the stalk base-change isomorphism is the canonical comparison. -/
theorem stalkBaseChangeComparisonIso_hom
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (ringPresheafOfComm 𝒪)) (x : X) :
    (stalkBaseChangeComparisonIso p ℱ x).hom = stalkBaseChangeComparison p ℱ x := sorry

/-- The inverse map of the stalk base-change isomorphism is the explicit comparison inverse. -/
theorem stalkBaseChangeComparisonIso_inv
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (ringPresheafOfComm 𝒪)) (x : X) :
    (stalkBaseChangeComparisonIso p ℱ x).inv = stalkBaseChangeComparisonInv p ℱ x := sorry

/-- The canonical comparison between extension of scalars on stalks and the stalk of the
extended presheaf is an isomorphism. -/
instance stalkBaseChangeComparison_isIso
    {X : TopCat.{u}} {𝒪 𝒪' : X.Presheaf CommRingCat.{u}} (p : 𝒪 ⟶ 𝒪')
    (ℱ : PresheafOfModules (ringPresheafOfComm 𝒪)) (x : X) :
    IsIso (stalkBaseChangeComparison p ℱ x) :=
  (stalkBaseChangeComparisonIso p ℱ x).isIso_hom

end TopCat.Presheaf
