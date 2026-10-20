/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.BaseChange.Comparison
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.BaseChange.Comparison.ScalarExtension.At
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Tensor
public import ReasLib.CategoryTheory.Monoidal.Functor.TensorComparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Scalar-extension facade for canonical `RHom` base change

This file only specializes the generic comparison to the canonical derived extension-of-scalars
functor.  The tensor comparison and the coherent closed comparisons remain explicit inputs: the
facade does not install a local monoidal instance or claim that an arbitrary pointwise family is
natural.

@stack 08I4
@stack 0E1X
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.DerivedCategory

namespace CategoryTheory.DerivedCategory.InternalHom.RHom.BaseChange.ScalarExtension

variable {R S : Type u} [CommRing R] [CommRing S]

/-- `08I4:` The canonical derived extension-of-scalars functor in the aligned module universe. -/
@[stacks 08I4 "derived scalar-extension functor for canonical RHom"]
noncomputable abbrev functor (σ : R →+* S) :
    DerivedCategory (ModuleCat.{u, u} R) ⥤
      DerivedCategory (ModuleCat.{u, u} S) :=
  ModuleCat.derivedExtensionOfScalars.{u, u, u} σ

/-- `08I4:` The tensor comparison required by the scalar-extension `RHom` facade. -/
@[stacks 08I4 "tensor comparison input for derived scalar extension"]
noncomputable abbrev TensorComparison (σ : R →+* S)
    [MonoidalCategory (DerivedCategory (ModuleCat.{u, u} R))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u, u} S))] :=
  Functor.TensorComparison (functor σ)

/-- `08I4:` The source bifunctor for scalar-extension base change of canonical `RHom`. -/
@[stacks 08I4 "scalar-extension RHom base-change source"]
noncomputable abbrev sourceFunctor (σ : R →+* S) [RHom.Has (A := R)] :=
  RHom.BaseChange.sourceFunctor (functor σ)

/-- `08I4:` The target bifunctor for scalar-extension base change of canonical `RHom`. -/
@[stacks 08I4 "scalar-extension RHom base-change target"]
noncomputable abbrev targetFunctor (σ : R →+* S) [RHom.Has (A := S)] :=
  RHom.BaseChange.targetFunctor (functor σ)

section Comparison

variable [MonoidalCategory (DerivedCategory (ModuleCat.{u, u} R))]
variable [MonoidalCategory (DerivedCategory (ModuleCat.{u, u} S))]
variable [RHom.Has (A := R)] [RHom.Has (A := S)]

/-- `0E1X:` The coherent scalar-extension comparison for canonical `RHom`. -/
@[stacks 0E1X, stacks 08I4 "scalar-extension RHom base-change comparison"]
noncomputable abbrev comparison
    (σ : R →+* S)
    (M : RHom.BifunctorComparison (A := R))
    (M' : RHom.BifunctorComparison (A := S))
    (T : TensorComparison σ) :
    sourceFunctor σ ⟶ targetFunctor σ :=
  RHom.BaseChange.comparison (functor σ) M M' T

/-- `0E1X:` The component of the scalar-extension comparison at `(K,L)`. -/
@[stacks 0E1X, stacks 08I4 "scalar-extension RHom base-change component"]
noncomputable abbrev comparisonApp
    (σ : R →+* S)
    (M : RHom.BifunctorComparison (A := R))
    (M' : RHom.BifunctorComparison (A := S))
    (T : TensorComparison σ)
    (K L : DerivedCategory (ModuleCat.{u, u} R)) :=
  RHom.BaseChange.comparisonApp (functor σ) M M' T K L

/-- `08I4:` Build the ambient tensor comparison required by `RHom` base change from explicit
two-variable derived-tensor model isomorphisms. -/
@[stacks 08I4 "scalar-extension tensor comparison from derived tensor models"]
noncomputable abbrev tensorComparisonOfModels
    (σ : R →+* S)
    (eR : ModuleCat.DerivedExtension.Tensor.derivedTensor R ≅
      MonoidalCategory.tensor (DerivedCategory (ModuleCat.{u, u} R)))
    (eS : ModuleCat.DerivedExtension.Tensor.derivedTensor S ≅
      MonoidalCategory.tensor (DerivedCategory (ModuleCat.{u, u} S))) :
    TensorComparison σ :=
  ModuleCat.DerivedExtension.Tensor.ambientTensorComparison σ eR eS

/-- `08I4:` The coherent scalar-extension `RHom` comparison assembled from explicit
derived-tensor model isomorphisms. -/
@[stacks 08I4 "scalar-extension RHom comparison from derived tensor models"]
noncomputable abbrev comparisonOfModels
    (σ : R →+* S)
    (M : RHom.BifunctorComparison (A := R))
    (M' : RHom.BifunctorComparison (A := S))
    (eR : ModuleCat.DerivedExtension.Tensor.derivedTensor R ≅
      MonoidalCategory.tensor (DerivedCategory (ModuleCat.{u, u} R)))
    (eS : ModuleCat.DerivedExtension.Tensor.derivedTensor S ≅
      MonoidalCategory.tensor (DerivedCategory (ModuleCat.{u, u} S))) :
    sourceFunctor σ ⟶ targetFunctor σ :=
  comparison σ M M' (tensorComparisonOfModels σ eR eS)

namespace FixedRight

/-- `08I4:` The aligned scalar-extension tensor comparison from two fixed-right model families. -/
@[stacks 08I4 "scalar-extension tensor comparison from fixed-right models"]
noncomputable abbrev tensorComparison
    (σ : R →+* S)
    (MR : DerivedTensor.Right.Monoidal.Model
      (C := ModuleCat.{u} R))
    (MS : DerivedTensor.Right.Monoidal.Model
      (C := ModuleCat.{u} S))
    (hR : ModuleCat.DerivedExtension.Tensor.ModelIsNatural R MR)
    (hS : ModuleCat.DerivedExtension.Tensor.ModelIsNatural S MS) :
    TensorComparison σ :=
  ModuleCat.DerivedExtension.Tensor.ambientTensorComparisonOfModels σ MR MS hR hS

/-- `08I4:` The aligned scalar-extension `RHom` comparison from fixed-right models. -/
@[stacks 08I4 "scalar-extension RHom comparison from fixed-right models"]
noncomputable abbrev comparison
    (σ : R →+* S)
    (M : RHom.BifunctorComparison (A := R))
    (M' : RHom.BifunctorComparison (A := S))
    (MR : DerivedTensor.Right.Monoidal.Model
      (C := ModuleCat.{u} R))
    (MS : DerivedTensor.Right.Monoidal.Model
      (C := ModuleCat.{u} S))
    (hR : ModuleCat.DerivedExtension.Tensor.ModelIsNatural R MR)
    (hS : ModuleCat.DerivedExtension.Tensor.ModelIsNatural S MS) :
    sourceFunctor σ ⟶ targetFunctor σ :=
  RHom.BaseChange.ScalarExtension.comparison σ M M'
    (tensorComparison σ MR MS hR hS)

end FixedRight

/-- `0E1X:` The component of the scalar-extension comparison at `(K,L)`. -/
@[simp, stacks 0E1X, stacks 08I4 "scalar-extension RHom base-change component"]
theorem comparison_app
    (σ : R →+* S)
    (M : RHom.BifunctorComparison (A := R))
    (M' : RHom.BifunctorComparison (A := S))
    (T : TensorComparison σ)
    (K L : DerivedCategory (ModuleCat.{u, u} R)) :
    (comparison σ M M' T).app (Opposite.op K, L) =
      comparisonApp σ M M' T K L :=
  RHom.BaseChange.comparison_app (functor σ) M M' T K L

/-- `08I4:` The model-assembled comparison has the corresponding generic component. -/
@[simp, stacks 08I4 "model-assembled scalar-extension RHom component"]
theorem comparisonOfModels_app
    (σ : R →+* S)
    (M : RHom.BifunctorComparison (A := R))
    (M' : RHom.BifunctorComparison (A := S))
    (eR : ModuleCat.DerivedExtension.Tensor.derivedTensor R ≅
      MonoidalCategory.tensor (DerivedCategory (ModuleCat.{u, u} R)))
    (eS : ModuleCat.DerivedExtension.Tensor.derivedTensor S ≅
      MonoidalCategory.tensor (DerivedCategory (ModuleCat.{u, u} S)))
    (K L : DerivedCategory (ModuleCat.{u, u} R)) :
    (comparisonOfModels σ M M' eR eS).app (Opposite.op K, L) =
      comparisonApp σ M M' (tensorComparisonOfModels σ eR eS) K L :=
  comparison_app σ M M' (tensorComparisonOfModels σ eR eS) K L

/-- `08I4:` Contravariant source naturality of the scalar-extension comparison. -/
@[reassoc, stacks 08I4 "scalar-extension RHom source naturality"]
theorem comparison_natural_source
    (σ : R →+* S)
    (M : RHom.BifunctorComparison (A := R))
    (M' : RHom.BifunctorComparison (A := S))
    (T : TensorComparison σ)
    {K₁ K₂ : DerivedCategory (ModuleCat.{u, u} R)} (f : K₂ ⟶ K₁)
    (L : DerivedCategory (ModuleCat.{u, u} R)) :
    (functor σ).map (RHom.map (A := R) f (𝟙 L)) ≫
        comparisonApp σ M M' T K₂ L =
      comparisonApp σ M M' T K₁ L ≫
        RHom.map (A := S) ((functor σ).map f) (𝟙 ((functor σ).obj L)) :=
  RHom.BaseChange.comparison_natural_source (functor σ) M M' T f L

/-- `08I4:` Covariant target naturality of the scalar-extension comparison. -/
@[reassoc, stacks 08I4 "scalar-extension RHom target naturality"]
theorem comparison_natural_target
    (σ : R →+* S)
    (M : RHom.BifunctorComparison (A := R))
    (M' : RHom.BifunctorComparison (A := S))
    (T : TensorComparison σ)
    (K : DerivedCategory (ModuleCat.{u, u} R))
    {L₁ L₂ : DerivedCategory (ModuleCat.{u, u} R)} (f : L₁ ⟶ L₂) :
    (functor σ).map (RHom.map (A := R) (𝟙 K) f) ≫
        comparisonApp σ M M' T K L₂ =
      comparisonApp σ M M' T K L₁ ≫
        RHom.map (A := S) (𝟙 ((functor σ).obj K)) ((functor σ).map f) :=
  RHom.BaseChange.comparison_natural_target (functor σ) M M' T K f

/-- `08I4:` Source naturality of the scalar-extension comparison assembled from tensor models. -/
@[reassoc, stacks 08I4 "model-assembled scalar-extension RHom source naturality"]
theorem comparisonOfModels_natural_source
    (σ : R →+* S)
    (M : RHom.BifunctorComparison (A := R))
    (M' : RHom.BifunctorComparison (A := S))
    (eR : ModuleCat.DerivedExtension.Tensor.derivedTensor R ≅
      MonoidalCategory.tensor (DerivedCategory (ModuleCat.{u, u} R)))
    (eS : ModuleCat.DerivedExtension.Tensor.derivedTensor S ≅
      MonoidalCategory.tensor (DerivedCategory (ModuleCat.{u, u} S)))
    {K₁ K₂ : DerivedCategory (ModuleCat.{u, u} R)} (f : K₂ ⟶ K₁)
    (L : DerivedCategory (ModuleCat.{u, u} R)) :
    (functor σ).map (RHom.map (A := R) f (𝟙 L)) ≫
        comparisonApp σ M M' (tensorComparisonOfModels σ eR eS) K₂ L =
      comparisonApp σ M M' (tensorComparisonOfModels σ eR eS) K₁ L ≫
        RHom.map (A := S) ((functor σ).map f) (𝟙 ((functor σ).obj L)) :=
  comparison_natural_source σ M M' (tensorComparisonOfModels σ eR eS) f L

/-- `08I4:` Target naturality of the scalar-extension comparison assembled from tensor models. -/
@[reassoc, stacks 08I4 "model-assembled scalar-extension RHom target naturality"]
theorem comparisonOfModels_natural_target
    (σ : R →+* S)
    (M : RHom.BifunctorComparison (A := R))
    (M' : RHom.BifunctorComparison (A := S))
    (eR : ModuleCat.DerivedExtension.Tensor.derivedTensor R ≅
      MonoidalCategory.tensor (DerivedCategory (ModuleCat.{u, u} R)))
    (eS : ModuleCat.DerivedExtension.Tensor.derivedTensor S ≅
      MonoidalCategory.tensor (DerivedCategory (ModuleCat.{u, u} S)))
    (K : DerivedCategory (ModuleCat.{u, u} R))
    {L₁ L₂ : DerivedCategory (ModuleCat.{u, u} R)} (f : L₁ ⟶ L₂) :
    (functor σ).map (RHom.map (A := R) (𝟙 K) f) ≫
        comparisonApp σ M M' (tensorComparisonOfModels σ eR eS) K L₂ =
      comparisonApp σ M M' (tensorComparisonOfModels σ eR eS) K L₁ ≫
        RHom.map (A := S) (𝟙 ((functor σ).obj K)) ((functor σ).map f) :=
  comparison_natural_target σ M M' (tensorComparisonOfModels σ eR eS) K f

end Comparison

end CategoryTheory.DerivedCategory.InternalHom.RHom.BaseChange.ScalarExtension
