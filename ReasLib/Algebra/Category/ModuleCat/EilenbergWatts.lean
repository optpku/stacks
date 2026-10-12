/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- The tensor-right functor is linear in its variable. -/
noncomputable def tensorRightLinear (N : ModuleCat.{u} R) :
    (tensorRight N).Linear R := inferInstance

/-- Tensoring on the right preserves finite colimits. -/
noncomputable def tensorRight_preservesFiniteColimits (N : ModuleCat.{u} R) :
    PreservesFiniteColimits (tensorRight N) := inferInstance

/-- Tensoring on the right preserves colimits indexed by any discrete type. -/
noncomputable def tensorRight_preservesColimitsOfShape_discrete (N : ModuleCat.{u} R)
    (I : Type u) : PreservesColimitsOfShape (Discrete I) (tensorRight N) := inferInstance

/-- The Eilenberg–Watts comparison component sends `m ⊗ x` to the image of `x`
under the morphism represented by `m`. -/
def tensorRightComparisonApp (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R)
    [F.Additive] [F.Linear R] (M : ModuleCat.{u} R) :
    (tensorRight (F.obj (of R R))).obj M ⟶ F.obj M :=
  ofHom (TensorProduct.lift
    ((homLinearEquiv (M := F.obj (of R R)) (N := F.obj M) (S := R)).toLinearMap ∘ₗ
      F.mapLinearMap R ∘ₗ (homLinearEquiv (M := of R R) (N := M) (S := R)).symm.toLinearMap ∘ₗ
      (LinearMap.lsmul R M).flip))

/-- The comparison component has the expected tensor-product formula. -/
theorem tensorRightComparisonApp_tmul (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R)
    [F.Additive] [F.Linear R] (M : ModuleCat.{u} R) (m : M) (x : F.obj (of R R)) :
    tensorRightComparisonApp F M (TensorProduct.tmul R m x) =
      (F.map (ofHom (LinearMap.toSpanSingleton R M m))).hom x := sorry

/-- Naturality of the comparison components. -/
theorem tensorRightComparisonApp_naturality (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R)
    [F.Additive] [F.Linear R] {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    (tensorRight (F.obj (of R R))).map f ≫ tensorRightComparisonApp F M' =
      tensorRightComparisonApp F M ≫ F.map f := sorry

/-- The Eilenberg–Watts comparison natural transformation. -/
def tensorRightComparison (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R)
    [F.Additive] [F.Linear R] : tensorRight (F.obj (of R R)) ⟶ F where
  app := tensorRightComparisonApp F
  naturality := fun _ _ f => tensorRightComparisonApp_naturality F f

/-- The component of the comparison transformation at a module. -/
theorem tensorRightComparison_app (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R)
    [F.Additive] [F.Linear R] (M : ModuleCat.{u} R) :
    (tensorRightComparison F).app M = tensorRightComparisonApp F M := sorry

/-- The comparison is invertible under the Eilenberg–Watts hypotheses. -/
instance isIso_tensorRightComparison (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R)
    [F.Additive] [F.Linear R] [PreservesFiniteColimits F]
    [∀ I : Type u, PreservesColimitsOfShape (Discrete I) F] :
    IsIso (tensorRightComparison F) := sorry

/-- The comparison is invertible exactly when the functor is tensoring by a module. -/
theorem isIso_tensorRightComparison_iff (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R)
    [F.Additive] [F.Linear R] :
    IsIso (tensorRightComparison F) ↔
      ∃ N : ModuleCat.{u} R, Nonempty (F ≅ tensorRight N) := sorry

end ModuleCat
