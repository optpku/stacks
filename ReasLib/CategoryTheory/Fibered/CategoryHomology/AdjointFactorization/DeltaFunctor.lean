/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryHomology.AdjointFactorization
public import ReasLib.CategoryTheory.Fibered.CategoryHomology.Bar.Complex
public import ReasLib.CategoryTheory.Homology.HomologicalDeltaFunctor.Coeffaceable
public import ReasLib.CategoryTheory.Homology.HomologicalDeltaFunctor.ExactComplex
public import ReasLib.CategoryTheory.Homology.HomologicalDeltaFunctor.Universal
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison-index homology as a homological delta functor

The comparison-index construction for a morphism of fibered categories is packaged here as a
resolution-independent homological delta functor.  The projective left-derived comparison remains
a separate computational companion in `AdjointFactorization`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.FiberedCategoryOver.AdjointFactorization

noncomputable section

universe u v w z

namespace CategoryTheory.FiberedCategoryOver.FiberHomology.AdjointFactorization

variable {B : Type u} [Category.{v} B]
variable {X Y : FiberedCategoryOver.{u, v, w, w} B}
variable (g : X ⟶ Y)
variable (J : GrothendieckTopology Y.total)
variable (K : GrothendieckTopology X.total)
variable [HasSheafify J AddCommGrpCat.{max w z}]
variable [HasSheafify K AddCommGrpCat.{max w z}]

/-- The comparison-index Bar complex, sheafified degreewise on the target total site. -/
@[stacks 08PK "sheafified comparison-index Bar complex"]
noncomputable def sheafComplexFunctor :
    Sheaf K AddCommGrpCat.{max w z} ⥤
      ChainComplex (Sheaf J AddCommGrpCat.{max w z}) ℕ :=
  sheafToPresheaf K AddCommGrpCat.{max w z} ⋙
    sourcePullbackFunctor g ⋙
      Bar.complexFunctor (overTarget g) ⋙
        (presheafToSheaf J AddCommGrpCat.{max w z}).mapHomologicalComplex
          (ComplexShape.down ℕ)

/-- The comparison-index sheafified Bar complex is additive in source sheaves. -/
@[stacks 08PK "additivity of sheafified comparison-index Bar complex"]
instance sheafComplexFunctor.additive : (sheafComplexFunctor g J K).Additive := sorry

/-- The comparison-index sheafified Bar complex preserves finite limits. -/
@[stacks 08PK "finite-limit preservation of sheafified comparison-index Bar complex"]
instance sheafComplexFunctor.preservesFiniteLimits :
    PreservesFiniteLimits (sheafComplexFunctor g J K) := sorry

/-- The comparison-index sheafified Bar complex preserves finite colimits. -/
@[stacks 08PK "finite-colimit preservation of sheafified comparison-index Bar complex"]
instance sheafComplexFunctor.preservesFiniteColimits :
    PreservesFiniteColimits (sheafComplexFunctor g J K) := sorry

/-- Exactness of the sheafified comparison-index Bar complex in source coefficients. -/
@[stacks 08PK "exactness of sheafified comparison-index Bar complex"]
theorem sheafComplexFunctor_exact :
    exactFunctor (Sheaf K AddCommGrpCat.{max w z})
      (ChainComplex (Sheaf J AddCommGrpCat.{max w z}) ℕ)
      (sheafComplexFunctor g J K) := sorry

/-- The sheafified comparison-index Bar complex bundled with its exactness property. -/
@[stacks 08PK "bundled exact sheafified comparison-index Bar complex"]
noncomputable def sheafComplexExactFunctor :
    Sheaf K AddCommGrpCat.{max w z} ⥤ₑ
      ChainComplex (Sheaf J AddCommGrpCat.{max w z}) ℕ :=
  ⟨sheafComplexFunctor g J K, sheafComplexFunctor_exact g J K⟩

/-- The comparison-index homological delta functor. -/
@[stacks 08PK "comparison-index homological delta functor"]
noncomputable def deltaFunctor :
    HomologicalDeltaFunctor
      (Sheaf K AddCommGrpCat.{max w z})
      (Sheaf J AddCommGrpCat.{max w z}) :=
  HomologicalDeltaFunctor.ExactComplex.functorBundled
    (sheafComplexExactFunctor g J K)

/-- Degree-`n` branch of the comparison-index delta functor. -/
@[simp, stacks 08PK "comparison-index delta functor degree formula"]
theorem deltaFunctor_obj (n : ℕ) :
    ((deltaFunctor g J K n).obj) =
      sheafComplexFunctor g J K ⋙
        HomologicalComplex.homologyFunctor
          (Sheaf J AddCommGrpCat.{max w z}) (ComplexShape.down ℕ) n := sorry

/-- The connecting morphism of the comparison-index delta functor is the boundary map of its
bundled exact Bar complex. -/
@[simp, stacks 08PK "comparison-index delta functor connecting formula"]
theorem deltaFunctor_δ
    {S : ShortComplex (Sheaf K AddCommGrpCat.{max w z})}
    (hS : S.ShortExact) (n : ℕ) :
    (deltaFunctor g J K).δ hS n =
      HomologicalDeltaFunctor.ExactComplex.connecting
        (sheafComplexExactFunctor g J K).1 hS n := sorry

/-- The degree branches of the comparison-index delta functor are the source-facing homology
sheaves already exposed by the coefficient API. -/
@[stacks 08PK "comparison-index delta functor and homology sheaf"]
theorem deltaFunctor_obj_isomorphic_sheafOfSheaf (n : ℕ) :
    IsIsomorphic ((deltaFunctor g J K n).obj)
      (sheafOfSheafFunctor.{u, v, w, z} g J K n) := sorry

/-- Objectwise comparison-index delta-functor homology and the source-facing homology sheaf. -/
@[stacks 08PK "comparison-index delta functor on a source sheaf"]
theorem deltaFunctor_obj_obj_isomorphic_sheafOfSheaf
    (F : Sheaf K AddCommGrpCat.{max w z}) (n : ℕ) :
    IsIsomorphic (((deltaFunctor g J K n).obj).obj F)
      (sheafOfSheaf.{u, v, w, z} g J K F n) := sorry

/-- Positive comparison-index homology is coeffaceable in source sheaves. -/
@[stacks 08PK "coeffaceability of positive comparison-index homology"]
theorem deltaFunctor_degree_isCoeffaceable (n : ℕ) (hn : 0 < n) :
    ((deltaFunctor g J K n).obj).IsCoeffaceable := sorry

/-- The comparison-index homological delta functor is universal. -/
@[stacks 08PK "universality of comparison-index homology"]
instance deltaFunctor.isUniversal :
    HomologicalDeltaFunctor.IsUniversal (deltaFunctor g J K) :=
  HomologicalDeltaFunctor.isUniversal_of_coeffaceable (deltaFunctor g J K)
    (fun n hn ↦ deltaFunctor_degree_isCoeffaceable g J K n hn)

variable [Functor.IsContinuous (toFunctor g) K J]
variable [
  ((toFunctor g).sheafPushforwardContinuous AddCommGrpCat.{max w z} K J).IsRightAdjoint]

/-- Degree-zero comparison-index homology is the lower shriek along `g`. -/
@[stacks 08PK "degree-zero comparison-index homology is lower shriek"]
theorem lowerShriek_isomorphic_deltaFunctor_zero :
    IsIsomorphic
      ((toFunctor g).sheafPullback AddCommGrpCat.{max w z} K J)
      ((deltaFunctor g J K 0).obj) := sorry

/-- Any universal homological delta functor extending `g_!` is degreewise isomorphic to the
comparison-index homology sheaf. -/
@[stacks 08PK "universal comparison-index lower shriek homology"]
theorem universal_degree_isomorphic
    (T : HomologicalDeltaFunctor
      (Sheaf K AddCommGrpCat.{max w z})
      (Sheaf J AddCommGrpCat.{max w z}))
    [T.IsUniversal]
    (h₀ : IsIsomorphic (T 0).obj
      ((toFunctor g).sheafPullback AddCommGrpCat.{max w z} K J))
    (n : ℕ) :
    IsIsomorphic (T n).obj
      (sheafOfSheafFunctor.{u, v, w, z} g J K n) := sorry

/-- Objectwise readout of the universal comparison-index lower-shriek homology theorem. -/
@[stacks 08PK "universal comparison-index lower shriek homology on an object"]
theorem universal_obj_isomorphic
    (T : HomologicalDeltaFunctor
      (Sheaf K AddCommGrpCat.{max w z})
      (Sheaf J AddCommGrpCat.{max w z}))
    [T.IsUniversal]
    (h₀ : IsIsomorphic (T 0).obj
      ((toFunctor g).sheafPullback AddCommGrpCat.{max w z} K J))
    (F : Sheaf K AddCommGrpCat.{max w z}) (n : ℕ) :
    IsIsomorphic ((T n).obj.obj F)
      (sheafOfSheaf.{u, v, w, z} g J K F n) := sorry

end CategoryTheory.FiberedCategoryOver.FiberHomology.AdjointFactorization
