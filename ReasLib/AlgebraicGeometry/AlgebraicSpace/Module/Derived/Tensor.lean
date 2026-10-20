/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Bifunctor

/-!
# Tensor totalization for étale modules on algebraic spaces

The ordinary tensor is the canonical structure-ring tensor transported from the commutative
presentation. Native module-sheaf coproducts provide the total tensor of unbounded complexes.
Fixed-right derived tensor exists unconditionally for this ordinary tensor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory AlgebraicGeometry ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Countable module-sheaf coproducts give the total tensor of unbounded étale complexes. -/
instance modulesHasMapBifunctor {S : Scheme.{u}} (X : AlgebraicSpace S)
    (K L : CochainComplex X.Modules ℤ) :
    HomologicalComplex.HasMapBifunctor K L
      (CategoryTheory.MonoidalCategory.curriedTensor X.Modules) (up ℤ) := by
  -- Local instance justification (proof-local temporary data): the canonical sheafification
  -- laws provide module-sheaf coproducts required by cochain totalization.
  letI := modulesHasSheafify X
  -- Local instance justification (proof-local temporary data): locally bijective maps are the
  -- sheafification equivalences used by the module-sheaf coproduct construction.
  letI := modulesWEqualsLocallyBijective X
  intro n
  infer_instance

/-- Fixed-right unbounded derived tensor products exist for modules on an algebraic space. -/
instance Modules.hasDerivedTensorRight {S : Scheme.{u}} (X : AlgebraicSpace S) :
    DerivedCategory.DerivedTensor.Right.Has (C := X.Modules) :=
  sorry

/-- Graded objects of `𝒪_X`-modules admit totalized tensor products. -/
instance modulesHasGradedTensor {S : Scheme.{u}} (X : AlgebraicSpace S)
    (G₁ G₂ : GradedObject ℤ (Modules X)) :
    GradedObject.HasTensor G₁ G₂ :=
  sorry

/-- Triple tensors of graded `𝒪_X`-modules preserve the inner coproduct in the first two
factors. -/
instance modulesHasGoodTensor₁₂ {S : Scheme.{u}} (X : AlgebraicSpace S)
    (G₁ G₂ G₃ : GradedObject ℤ (Modules X)) :
    GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃ :=
  sorry

/-- Triple tensors of graded `𝒪_X`-modules preserve the inner coproduct in the last two
factors. -/
instance modulesHasGoodTensor₂₃ {S : Scheme.{u}} (X : AlgebraicSpace S)
    (G₁ G₂ G₃ : GradedObject ℤ (Modules X)) :
    GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃ :=
  sorry

/-- Quadruple tensors of graded `𝒪_X`-modules satisfy the extension condition. -/
instance modulesHasTensor₄ {S : Scheme.{u}} (X : AlgebraicSpace S)
    (G₁ G₂ G₃ G₄ : GradedObject ℤ (Modules X)) :
    GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄ :=
  sorry

/-- Two-variable unbounded derived tensor products exist for modules on an algebraic space. -/
instance hasDerivedTensorBifunctor {S : Scheme.{u}} (X : AlgebraicSpace S) :
    DerivedTensor.Bifunctor.Has (C := Modules X) :=
  sorry

/-- The two-variable derived tensor is a fixed-right left-derived functor. -/
instance hasDerivedTensorRightCompatible {S : Scheme.{u}} (X : AlgebraicSpace S)
    (E : ModuleDerived X) :
    DerivedTensor.Bifunctor.Right.Compatible E :=
  sorry

namespace DerivedQCoh

/-- The canonical monoidal structure on étale modules over an algebraic space. -/
protected noncomputable abbrev modulesMonoidalCategory {S : Scheme.{u}} (X : AlgebraicSpace S) :
    MonoidalCategory X.Modules :=
  AlgebraicGeometry.AlgebraicSpace.Modules.instMonoidalCategory X

/-- Tensoring étale modules over an algebraic space is additive in each variable. -/
protected abbrev modulesMonoidalPreadditive {S : Scheme.{u}} (X : AlgebraicSpace S) :
    MonoidalPreadditive X.Modules :=
  AlgebraicGeometry.AlgebraicSpace.modulesMonoidalPreadditive X

/-- The tensor bicomplex of unbounded étale cochain complexes admits totalization. -/
protected abbrev modulesHasMapBifunctor {S : Scheme.{u}} (X : AlgebraicSpace S)
    (K L : CochainComplex X.Modules ℤ) :
    HomologicalComplex.HasMapBifunctor K L
      (CategoryTheory.MonoidalCategory.curriedTensor X.Modules) (up ℤ) :=
  AlgebraicGeometry.AlgebraicSpace.modulesHasMapBifunctor X K L

/-- Fixed-right unbounded derived tensor exists for étale modules over an algebraic space. -/
protected abbrev hasDerivedTensorRight {S : Scheme.{u}} (X : AlgebraicSpace S) :
    DerivedCategory.DerivedTensor.Right.Has (C := X.Modules) :=
  AlgebraicGeometry.AlgebraicSpace.Modules.hasDerivedTensorRight X

/-- Quasi-coherent cohomology is a triangulated subcategory of `D(𝒪_X)`. -/
instance derivedQuasiCoherent_isTriangulated {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (derivedQuasiCoherentModuleProperty X).IsTriangulated :=
  sorry


end DerivedQCoh

end AlgebraicGeometry.AlgebraicSpace
