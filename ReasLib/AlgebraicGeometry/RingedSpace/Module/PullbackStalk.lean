/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk.BaseChange
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk.Pullback
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InverseImage
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback of module-sheaf stalks on ringed spaces

This file owns the concrete scalar-extension comparison between a pulled-back module sheaf and
its stalk.  General sheaf and presheaf comparison infrastructure remains in the neutral support
modules it imports.
-/

@[expose] public section

open AlgebraicGeometry.RingedSpace.Hom

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

/-- The topological inverse image of a module sheaf, before extending scalars to the structure
sheaf of the source ringed space. -/
@[stacks 03D6 "topological inverse image of a module sheaf"]
noncomputable abbrev inverseImageModule (𝒢 : Y.Modules) :
    SheafOfModules (TopCat.Sheaf.pullbackRing f.hom.base Y.sheaf).ringSheafOfComm :=
  (SheafOfModules.pullback
    (TopCat.Sheaf.commRingSheafPullbackUnit f.hom.base Y.sheaf)).obj 𝒢

/-- The map from the stalk of the inverse-image structure sheaf to the structure-sheaf stalk
of the source ringed space. -/
@[stacks 008H "inverse-image structure map on stalks"]
noncomputable abbrev inverseImageStalkMap (x : X) :
    (TopCat.Sheaf.pullbackRing f.hom.base Y.sheaf).presheaf.stalk x →+*
      X.presheaf.stalk x :=
  (((TopCat.Presheaf.stalkFunctor CommRingCat x).map
    (inverseImageStructureSheafHomComm f).hom).hom)

/-- The local ring map of a ringed-space morphism factors through the stalk of the topological
inverse image of the target structure sheaf. -/
@[stacks 008H "factorization of the local ring map"]
theorem stalkMap_factorization (x : X) :
    (inverseImageStalkMap f x).comp
        (TopCat.Sheaf.pullbackStalkRingMap f.hom.base Y.sheaf x) =
      (f.hom.stalkMap x).hom := sorry

/-- The ringed-space pullback of module sheaves factors as topological inverse image followed
by extension of scalars to the source structure sheaf. -/
@[stacks 03D6 "ringed-space module pullback factorization"]
noncomputable def pullbackFactorizationIso :
    pullback f ≅
      SheafOfModules.pullback
          (TopCat.Sheaf.commRingSheafPullbackUnit f.hom.base Y.sheaf) ⋙
        SheafOfModules.ChangeOfRings.extendScalars
          (TopCat.Sheaf.ringSheafOfCommMap
            (inverseImageStructureSheafHomComm f)) :=
  SheafOfModules.RingedSite.InverseImage.Factorization.pullbackIso
    (J := Opens.grothendieckTopology Y.carrier)
    (K := Opens.grothendieckTopology X.carrier)
    (Opens.map f.hom.base) (commRingSheafPushforwardMap f)

/-- On stalks, `pullbackFactorizationIso` identifies the ringed-space pullback with the explicit
same-space extension-of-scalars construction. -/
@[stacks 03D6 "stalk of the module pullback factorization"]
noncomputable def pullbackStalkFactorIso (𝒢 : Y.Modules) (x : X) :
    RingedSpace.stalkModuleCat ((pullback f).obj 𝒢) x ≅
      TopCat.Sheaf.sheafModuleBaseChangeTarget
        (inverseImageStructureSheafHomComm f) (inverseImageModule f 𝒢) x :=
  (RingedSpace.stalkModuleFunctor (X := X) x).mapIso
      ((pullbackFactorizationIso f).app 𝒢) ≪≫
    (RingedSpace.stalkModuleFunctor (X := X) x).mapIso
      ((SheafOfModules.ChangeOfRings.pullbackIso
          (TopCat.Sheaf.ringSheafOfCommMap
            (inverseImageStructureSheafHomComm f))).symm.app
            (inverseImageModule f 𝒢) ≪≫
        (SheafOfModules.pullbackIso
          (TopCat.Sheaf.commRingSheafHomOverId
            (inverseImageStructureSheafHomComm f))).app (inverseImageModule f 𝒢))

/-- Extension along the local ring map is the iterated extension along the topological
pullback-stalk map and the inverse-image structure map. -/
@[stacks 008H "scalar extension along the factored local ring map"]
noncomputable def pullbackStalkExtensionIso (𝒢 : Y.Modules) (x : X) :
    (ModuleCat.extendScalars (f.hom.stalkMap x).hom).obj
        (RingedSpace.stalkModuleCat 𝒢 (f.hom.base x)) ≅
      (ModuleCat.extendScalars (inverseImageStalkMap f x)).obj
        ((ModuleCat.extendScalars
          (TopCat.Sheaf.pullbackStalkRingMap f.hom.base Y.sheaf x)).obj
            (RingedSpace.stalkModuleCat 𝒢 (f.hom.base x))) :=
  eqToIso (congrArg
      (fun k : Y.presheaf.stalk (f.hom.base x) →+* X.presheaf.stalk x ↦
        (ModuleCat.extendScalars k).obj
          (RingedSpace.stalkModuleCat 𝒢 (f.hom.base x)))
      (stalkMap_factorization f x).symm) ≪≫
    (ModuleCat.extendScalarsComp
      (TopCat.Sheaf.pullbackStalkRingMap f.hom.base Y.sheaf x)
      (inverseImageStalkMap f x)).app
        (RingedSpace.stalkModuleCat 𝒢 (f.hom.base x))

/-- The additive stalk map underlying the pullback comparison, obtained from the unit of the
pullback–pushforward adjunction for module sheaves. -/
@[stacks 05V5 "ringed-space module pullback stalk scalar-extension unit"]
noncomputable abbrev pullbackStalkUnitHom (𝒢 : Y.Modules) (x : X) :
    TopCat.Presheaf.stalk 𝒢.val.presheaf (f.hom.base x) ⟶
      TopCat.Presheaf.stalk ((pullback f).obj 𝒢).val.presheaf x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f.hom.base x)).map
      ((SheafOfModules.toSheaf Y.ringCatSheaf).map
        ((SheafOfModules.pullbackPushforwardAdjunction
          (RingedSpace.Hom.toRingCatSheafHom f)).unit.app 𝒢)).hom ≫
    TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.hom.base
      ((pullback f).obj 𝒢).val.presheaf x

/-- The unit-induced stalk map is semilinear for the local ring map attached to `f`. -/
@[stacks 05V5 "ringed-space module pullback stalk unit semilinearity"]
theorem pullbackStalkUnitHom_smul (𝒢 : Y.Modules) (x : X)
    (r : Y.presheaf.stalk (f.hom.base x))
    (m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      𝒢.val.presheaf (f.hom.base x)) :
    pullbackStalkUnitHom f 𝒢 x (r • m) =
      f.hom.stalkMap x r • pullbackStalkUnitHom f 𝒢 x m := sorry
/- Proof strategy: represent `r` and `m` by germs on a common neighbourhood of `f.hom.base x`.
Use `TopCat.Presheaf.stalkFunctor_map_germ_apply` and
`TopCat.Presheaf.stalkPushforward_germ` to compute `pullbackStalkUnitHom` on that germ, then use
the sectionwise linearity of the unit of
`SheafOfModules.pullbackPushforwardAdjunction (RingedSpace.Hom.toRingCatSheafHom f)`.  Rewrite the
resulting scalar map with `PresheafedSpace.stalkMap_germ` and the defining adjunction equation for
`RingedSpace.Hom.toRingCatSheafHom f`; these identify it with `f.hom.stalkMap x`. -/

/-- The unit-induced stalk map, regarded as a linear map after restricting scalars along the
local-ring map of `f`.  Naming this conversion keeps the scalar restriction local and avoids a
noncanonical global module instance for the target. -/
@[stacks 05V5 "restricted ringed-space module pullback stalk unit"]
noncomputable def pullbackStalkUnitHomRestricted (𝒢 : Y.Modules) (x : X) :
    RingedSpace.stalkModuleCat 𝒢 (f.hom.base x) ⟶
      (ModuleCat.restrictScalars (f.hom.stalkMap x).hom).obj
        (RingedSpace.stalkModuleCat ((pullback f).obj 𝒢) x) :=
  (ModuleCat.semilinearMapAddEquiv (f.hom.stalkMap x).hom
    (RingedSpace.stalkModuleCat 𝒢 (f.hom.base x))
    (RingedSpace.stalkModuleCat ((pullback f).obj 𝒢) x))
    { toFun := pullbackStalkUnitHom f 𝒢 x
      map_add' := (pullbackStalkUnitHom f 𝒢 x).hom.map_add
      map_smul' := pullbackStalkUnitHom_smul f 𝒢 x }

/-- The canonical morphism from the scalar extension of `𝒢_{f(x)}` to the stalk of `pullback f𝒢` at
`x`. -/
@[stacks 05V5 "ringed-space module pullback stalk comparison"]
noncomputable def pullbackStalkComparison (𝒢 : Y.Modules) (x : X) :
    (ModuleCat.extendScalars (f.hom.stalkMap x).hom).obj
        (RingedSpace.stalkModuleCat 𝒢 (f.hom.base x)) ⟶
      RingedSpace.stalkModuleCat ((pullback f).obj 𝒢) x :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars (f.hom.stalkMap x).hom
    (pullbackStalkUnitHomRestricted f 𝒢 x)

/-- The forward pullback-stalk comparison written through the topological inverse-image and
same-space base-change APIs. -/
@[stacks 05V5 "factored ringed-space module pullback stalk comparison"]
noncomputable def pullbackStalkComparisonFactored (𝒢 : Y.Modules) (x : X) :
    (ModuleCat.extendScalars (f.hom.stalkMap x).hom).obj
        (RingedSpace.stalkModuleCat 𝒢 (f.hom.base x)) ⟶
      RingedSpace.stalkModuleCat ((pullback f).obj 𝒢) x :=
  (pullbackStalkExtensionIso f 𝒢 x).hom ≫
    (ModuleCat.extendScalars (inverseImageStalkMap f x)).map
      (TopCat.Sheaf.modulePullbackStalkComparison
        f.hom.base Y.sheaf x 𝒢) ≫
    TopCat.Sheaf.moduleBaseChangeStalkComparison
      (inverseImageStructureSheafHomComm f) (inverseImageModule f 𝒢) x ≫
    (pullbackStalkFactorIso f 𝒢 x).inv

/-- The factored forward comparison is the source-facing canonical comparison. -/
@[simp, stacks 05V5 "ringed-space module pullback stalk comparison factorization law"]
theorem pullbackStalkComparisonFactored_eq (𝒢 : Y.Modules) (x : X) :
    pullbackStalkComparisonFactored f 𝒢 x = pullbackStalkComparison f 𝒢 x := sorry

/-- The explicit inverse of the canonical pullback-stalk comparison. -/
@[stacks 05V5 "inverse ringed-space module pullback stalk comparison"]
noncomputable def pullbackStalkComparisonInv (𝒢 : Y.Modules) (x : X) :
    RingedSpace.stalkModuleCat ((pullback f).obj 𝒢) x ⟶
      (ModuleCat.extendScalars (f.hom.stalkMap x).hom).obj
        (RingedSpace.stalkModuleCat 𝒢 (f.hom.base x)) :=
  (pullbackStalkFactorIso f 𝒢 x).hom ≫
    TopCat.Sheaf.moduleBaseChangeStalkComparisonInv
      (inverseImageStructureSheafHomComm f) (inverseImageModule f 𝒢) x ≫
    (ModuleCat.extendScalars (inverseImageStalkMap f x)).map
      (TopCat.Sheaf.modulePullbackStalkComparisonInv
        f.hom.base Y.sheaf x 𝒢) ≫
    (pullbackStalkExtensionIso f 𝒢 x).inv

/-- The pullback-stalk comparison followed by its explicit inverse is the identity. -/
@[simp, stacks 05V5 "ringed-space module pullback stalk forward-inverse law"]
theorem pullbackStalkComparison_hom_inv_id (𝒢 : Y.Modules) (x : X) :
    pullbackStalkComparison f 𝒢 x ≫ pullbackStalkComparisonInv f 𝒢 x = 𝟙 _ := sorry

/-- The explicit inverse followed by the pullback-stalk comparison is the identity. -/
@[simp, stacks 05V5 "ringed-space module pullback stalk inverse-forward law"]
theorem pullbackStalkComparison_inv_hom_id (𝒢 : Y.Modules) (x : X) :
    pullbackStalkComparisonInv f 𝒢 x ≫ pullbackStalkComparison f 𝒢 x = 𝟙 _ := sorry

/-- The canonical isomorphism from scalar extension of `𝒢_{f(x)}` to the stalk of `pullback f𝒢` at
`x`. -/
@[stacks 05V5 "ringed-space module pullback stalk isomorphism"]
noncomputable def pullbackStalkIso (𝒢 : Y.Modules) (x : X) :
    (ModuleCat.extendScalars (f.hom.stalkMap x).hom).obj
        (RingedSpace.stalkModuleCat 𝒢 (f.hom.base x)) ≅
      RingedSpace.stalkModuleCat ((pullback f).obj 𝒢) x where
  hom := pullbackStalkComparison f 𝒢 x
  inv := pullbackStalkComparisonInv f 𝒢 x
  hom_inv_id := pullbackStalkComparison_hom_inv_id f 𝒢 x
  inv_hom_id := pullbackStalkComparison_inv_hom_id f 𝒢 x

/-- The canonical pullback-stalk comparison is an isomorphism. -/
@[stacks 05V5 "ringed-space module pullback stalk comparison is an isomorphism", instance]
instance pullbackStalkComparison_isIso (𝒢 : Y.Modules) (x : X) :
    IsIso (pullbackStalkComparison f 𝒢 x) := sorry

/-- The forward morphism of `pullbackStalkIso` is the canonical pullback-stalk comparison. -/
@[simp, stacks 05V5 "ringed-space module pullback stalk isomorphism hom"]
theorem pullbackStalkIso_hom (𝒢 : Y.Modules) (x : X) :
    (pullbackStalkIso f 𝒢 x).hom = pullbackStalkComparison f 𝒢 x := sorry

/-- The inverse morphism of `pullbackStalkIso` is the explicit pullback-stalk inverse. -/
@[simp, stacks 05V5 "ringed-space module pullback stalk isomorphism inverse"]
theorem pullbackStalkIso_inv (𝒢 : Y.Modules) (x : X) :
    (pullbackStalkIso f 𝒢 x).inv = pullbackStalkComparisonInv f 𝒢 x := sorry

end AlgebraicGeometry.RingedSpace.Hom
