/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.FunctionField
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive
public import ReasLib.AlgebraicGeometry.Scheme.Normal

/-!
# Extending generic-fiber maps to reflexive hulls

This file defines the height-one stalk condition for a map on the generic fiber of coherent
module sheaves and states its equivalence with extension to a reflexive hull.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X]

section ReflexiveHullExtension

variable [IsLocallyNoetherian X]

/-- A map between the generic stalks extends to the reflexive hull when it is induced, after the
canonical map to the double dual, by a morphism of module sheaves. -/
abbrev extendsToReflexiveHullAtGenericPoint
    (ℱ 𝒢 : X.Modules) [ℱ.IsCoherent] [𝒢.IsCoherent]
    (T : RingedSpace.stalkModuleCat 𝒢 (genericPoint X) ⟶
      RingedSpace.stalkModuleCat ℱ (genericPoint X)) : Prop :=
  ∃ φ : 𝒢 ⟶ reflexiveHull ℱ,
    RingedSpace.moduleStalkHom (genericPoint X) φ =
      T ≫ RingedSpace.moduleStalkHom (genericPoint X) (toReflexiveHull ℱ)

end ReflexiveHullExtension

/-- At a point `x`, the prescribed generic-stalk map carries the image of the canonical map from
the stalk of `𝒢` into the image of the canonical map from the stalk of `ℱ`. -/
def heightOneStalkImageConditionAt
    (ℱ 𝒢 : X.Modules)
    (T : RingedSpace.stalkModuleCat 𝒢 (genericPoint X) ⟶
      RingedSpace.stalkModuleCat ℱ (genericPoint X))
    (x : X) : Prop :=
  (LinearMap.comp
      (((ModuleCat.restrictScalars
        (algebraMap (X.presheaf.stalk x) X.functionField)).map T).hom)
      (stalkToFunctionField 𝒢 x).hom).range ≤
    (stalkToFunctionField ℱ x).hom.range

/-- A map of generic stalks satisfies the height-one extension condition when its image condition
holds at every point whose local ring has Krull dimension one. -/
def heightOneStalkConditionForExtension
    (ℱ 𝒢 : X.Modules)
    (T : RingedSpace.stalkModuleCat 𝒢 (genericPoint X) ⟶
      RingedSpace.stalkModuleCat ℱ (genericPoint X)) : Prop :=
  ∀ x : X, ringKrullDim (X.presheaf.stalk x) = 1 →
    heightOneStalkImageConditionAt ℱ 𝒢 T x

/-- The global height-one extension condition gives its canonical stalk-image inclusion at each
one-dimensional point. -/
theorem heightOneStalkConditionForExtension_apply
    (ℱ 𝒢 : X.Modules)
    (T : RingedSpace.stalkModuleCat 𝒢 (genericPoint X) ⟶
      RingedSpace.stalkModuleCat ℱ (genericPoint X))
    (hT : heightOneStalkConditionForExtension ℱ 𝒢 T)
    (x : X) (hx : ringKrullDim (X.presheaf.stalk x) = 1) :
    (LinearMap.comp
        (((ModuleCat.restrictScalars
          (algebraMap (X.presheaf.stalk x) X.functionField)).map T).hom)
        (stalkToFunctionField 𝒢 x).hom).range ≤
      (stalkToFunctionField ℱ x).hom.range :=
  hT x hx

section ReflexiveHullExtension

variable [IsLocallyNoetherian X]

/-- On an integral locally Noetherian normal scheme, a map between generic stalks of coherent
module sheaves extends to the reflexive hull exactly when it satisfies the canonical stalk-image
condition at every one-dimensional local ring. -/
theorem extendsToReflexiveHullAtGenericPoint_iff_forall_heightOne
    (ℱ 𝒢 : X.Modules) [ℱ.IsCoherent] [𝒢.IsCoherent]
    (hXnormal : X.isNormal)
    (T : RingedSpace.stalkModuleCat 𝒢 (genericPoint X) ⟶
      RingedSpace.stalkModuleCat ℱ (genericPoint X)) :
    extendsToReflexiveHullAtGenericPoint ℱ 𝒢 T ↔
      heightOneStalkConditionForExtension ℱ 𝒢 T := sorry

end ReflexiveHullExtension

end AlgebraicGeometry.Scheme.Modules
