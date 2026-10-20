/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive.Extension
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

/- Lemma 31.12.14: on an integral locally Noetherian normal scheme, a generic-stalk map between
coherent module sheaves extends to the reflexive hull if and only if it carries the canonical
image of every one-dimensional stalk into the corresponding canonical image. -/
@[stacks 0AY7] #check
  (AlgebraicGeometry.Scheme.Modules.extendsToReflexiveHullAtGenericPoint_iff_forall_heightOne :
    ∀ {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
      (ℱ 𝒢 : X.Modules) [ℱ.IsCoherent] [𝒢.IsCoherent]
      (hXnormal : X.isNormal)
      (T : RingedSpace.stalkModuleCat 𝒢 (genericPoint X) ⟶
        RingedSpace.stalkModuleCat ℱ (genericPoint X)),
      AlgebraicGeometry.Scheme.Modules.extendsToReflexiveHullAtGenericPoint ℱ 𝒢 T ↔
        AlgebraicGeometry.Scheme.Modules.heightOneStalkConditionForExtension ℱ 𝒢 T)
