/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.Derived.IdealPower

/-! The canonical ideal-power tensor tower, with its tensor-polymorphic interface. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProEt Opposite

noncomputable section

universe u w

variable {Λ : Type w} [CommRing Λ]
variable {X : Scheme.{u}}
variable [HasWeakSheafify (topology X) (ModuleCat.{w} Λ)]
variable [Abelian (Sheaf (topology X) (ModuleCat.{w} Λ))]
variable [HasDerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))]
variable [MonoidalCategory (Sheaf (topology X) (ModuleCat.{w} Λ))]

-- Local declaration justification (instance diamond): module sheaves inherit
-- `HasZeroMorphisms` and `Preadditive` through `FullSubcategory`, whereas derived
-- tensor and exact derived functors use `Abelian.toPreadditive`. Suppress the
-- two embedding instances only while elaborating the affected declarations.
-- Parameter blocks restore both instances before any public declaration; each
-- declaration below uses its own scoped suppression.
attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory Preadditive.fullSubcategory
variable [MonoidalPreadditive (Sheaf (topology X) (ModuleCat.{w} Λ))]
variable [∀ (K L : CochainComplex (Sheaf (topology X) (ModuleCat.{w} Λ)) ℤ),
  HomologicalComplex.HasMapBifunctor K L
    (curriedTensor (Sheaf (topology X) (ModuleCat.{w} Λ))) (ComplexShape.up ℤ)]
variable [DerivedCategory.DerivedTensor.Right.Has
  (C := Sheaf (topology X) (ModuleCat.{w} Λ))]
variable [DerivedCategory.DerivedTensor.Left.Has
  (C := Sheaf (topology X) (ModuleCat.{w} Λ))]

attribute [instance] ObjectProperty.instHasZeroMorphismsFullSubcategory Preadditive.fullSubcategory

attribute [-instance] ObjectProperty.instHasZeroMorphismsFullSubcategory Preadditive.fullSubcategory in
#check (AlgebraicGeometry.Scheme.ProEt.idealPowerTensorSystem :
  ∀ (I : Ideal Λ) (K : DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))),
    SequentialInverseSystem (DerivedCategory (Sheaf (topology X) (ModuleCat.{w} Λ))))

end
