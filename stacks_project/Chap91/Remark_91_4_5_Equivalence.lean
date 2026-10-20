/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Equivalence

/-!
# Equivalence between trivialized first-order thickenings and modules

This source-facing module preserves the historical names through typed checks
of the reusable equivalence API.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.RingedSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RingedSpace.IsFirstOrderThickening

#check (idealFunctor : ∀ (X : RingedSpace.{u}),
  Trivialized X ⥤ (X.Modules)ᵒᵖ)
#check (ofModuleFunctor : ∀ (X : RingedSpace.{u}),
  (X.Modules)ᵒᵖ ⥤ Trivialized X)
#check (unitHom : ∀ {X : RingedSpace.{u}} (T : Trivialized X),
  T ⟶ ofModule (RingedSpace.Hom.idealModule T.inclusion))
#check (homEquiv : ∀ {X : RingedSpace.{u}} (T₁ T₂ : Trivialized X),
  (T₁ ⟶ T₂) ≃
    (RingedSpace.Hom.idealModule T₂.inclusion ⟶
      RingedSpace.Hom.idealModule T₁.inclusion))
#check (ofModule_idealIso : ∀ {X : RingedSpace.{u}} (M : X.Modules),
  RingedSpace.Hom.idealModule (inclusion M) ≅ M)
#check (modulesEquiv : ∀ (X : RingedSpace.{u}),
  Trivialized X ≌ (X.Modules)ᵒᵖ)

end AlgebraicGeometry.RingedSpace.IsFirstOrderThickening
