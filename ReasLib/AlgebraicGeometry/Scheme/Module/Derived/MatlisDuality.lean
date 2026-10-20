/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import ReasLib.Algebra.Module.Injective.Hull
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent.Support
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Local
public import ReasLib.AlgebraicGeometry.Scheme.Regular

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry.SchemeOverField

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

open DerivedCategory.DerivedTensor RingedSpace RingedSpace.ModuleDerived

/-- On a regular scheme of finite type over a field, a coherent module supported at a closed
point represents the shifted derived-global-sections functor determined by a coherent module
whose stalk is its Matlis dual. -/
theorem homIsoTensorMatlisDualAt
    {k : Type u} [Field k] (X : SchemeOverField k)
    [Hom.FiniteType X.hom] [Regular X.left]
    (x : X.left) (hx : x ∈ closedPoints X.left)
    (F F' : CohSupportedOn X.left.toRingedSpace {x})
    (E : Type u) [AddCommGroup E] [Module (stalkRing X x) E]
    [Module.Injective (stalkRing X x) E]
    (ι : IsLocalRing.ResidueField (stalkRing X x) →ₗ[stalkRing X x] E)
    (hι : ι.IsInjectiveHull)
    (h_dual : stalkModuleCat F'.obj.obj x ≅
      ModuleCat.of (stalkRing X x) (stalkModuleCat F.obj.obj x →ₗ[stalkRing X x] E))
    (d : ℕ) (h_dimension : ringKrullDim (stalkRing X x) = (d : WithBot ℕ∞)) :
    Nonempty
      ((Perfect.ι ⋙
          preadditiveCoyoneda.obj
            (op ((DerivedCategory.singleFunctor X.left.Modules 0).obj F.obj.obj))) ≅
        (Perfect.ι ⋙
          Right.functor
            (((DerivedCategory.singleFunctor X.left.Modules 0).obj F'.obj.obj)⟦-(d : ℤ)⟧) ⋙
          moduleDerivedCohomologyFunctor X.left.toRingedSpace 0 ⋙
          forget₂ (ModuleCat (globalSectionsRing X.left.toRingedSpace)) AddCommGrpCat.{u} ⋙
          AddCommGrpCat.uliftFunctor.{u + 1, u})) := sorry

end AlgebraicGeometry.Scheme
