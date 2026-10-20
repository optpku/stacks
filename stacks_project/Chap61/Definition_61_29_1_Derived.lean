/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.Derived.Basic

/-! Source-facing bridge for the reusable pro-étale derived-category API. -/

@[expose] public section

open CategoryTheory
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u v

#check @AlgebraicGeometry.Scheme.ProetaleModuleSheaf
#check (AlgebraicGeometry.Scheme.proetaleModuleSheaf_eq :
  ∀ (X : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    [HasWeakSheafify (ProEt.topology X) (ModuleCat.{v} Λ)],
    ProetaleModuleSheaf X Λ = Sheaf (ProEt.topology X) (ModuleCat.{v} Λ))
#check @AlgebraicGeometry.Scheme.ProetaleDerived
#check @AlgebraicGeometry.Scheme.proetaleDerived_def
#check @AlgebraicGeometry.Scheme.ProetaleDerived.constantCoefficientRing
#check @AlgebraicGeometry.Scheme.ProetaleDerived.constantCoefficientRing_ringSheafIso
#check @AlgebraicGeometry.Scheme.ProetaleDerived.constantCoefficientRing_ringSheafIso_hom_eq
#check @AlgebraicGeometry.Scheme.ProetaleDerived.toConstantModuleFunctor
#check @AlgebraicGeometry.Scheme.ProetaleDerived.toConstantModuleFunctor_obj
#check @AlgebraicGeometry.Scheme.ProetaleDerived.reduction
#check @AlgebraicGeometry.Scheme.ProetaleDerived.reduction_eq
#check @AlgebraicGeometry.Scheme.ProetaleDerived.hasDerivedCategory_constantCoefficient
#check @AlgebraicGeometry.Scheme.ProetaleDerived.toConstantModuleFunctor_additive
#check @AlgebraicGeometry.Scheme.ProetaleDerived.toConstantModuleFunctor_preservesFiniteLimits
#check @AlgebraicGeometry.Scheme.ProetaleDerived.toConstantModuleFunctor_preservesFiniteColimits
#check @AlgebraicGeometry.Scheme.ProetaleDerived.toConstantModuleDerived
#check @AlgebraicGeometry.Scheme.ProetaleDerived.toConstantModuleDerived_eq
#check @AlgebraicGeometry.Scheme.ProetaleDerived.constantCoefficientToSheafify
#check @AlgebraicGeometry.Scheme.ProetaleDerived.constantCoefficientIdeal
#check @AlgebraicGeometry.Scheme.ProetaleDerived.constantCoefficientIdeal_eq
#check @AlgebraicGeometry.Scheme.ProetaleDerived.IsDerivedCompleteWithRespectTo
#check @AlgebraicGeometry.Scheme.ProetaleDerived.isDerivedCompleteWithRespectTo_iff
