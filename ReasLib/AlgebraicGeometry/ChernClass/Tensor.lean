/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChernClass.Total
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.SplittingPrinciple

@[expose] public section

open CategoryTheory
open scoped BigOperators

noncomputable section

universe u v w x y z

namespace AlgebraicGeometry.ChernClass.TotalChernClass

/-- For a finite locally free module `E` of rank `r` and an invertible module `L`, the
coefficient of degree `i` in the total Chern class of `E ⊗ L` is the corresponding
binomial sum of the Chern classes of `E` and powers of the first Chern class of `L`. -/
theorem coeff_tensor_invertible
    {C : Type u} [Category.{v} C] (toScheme : C ⥤ Scheme.{w})
    (A : Cᵒᵖ ⥤ RingCat.{x})
    (Agrade : ∀ X, ℕ → Submodule ℤ (A.obj (Opposite.op X)))
    [∀ X, GradedAlgebra (Agrade X)]
    (S : CohomologyTheory toScheme A Agrade)
    (c : TotalChernClass toScheme A Agrade S.firstChernClass)
    (X : C) (E L : (toScheme.obj X).Modules) (r i : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    [Scheme.Modules.Invertible L] :
    let hE : E.IsFiniteLocallyFree :=
      Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank r E
    let hLRank : L.IsFiniteLocallyFreeOfRank 1 :=
      Scheme.Modules.isFiniteLocallyFreeOfRankOne_of_invertible L
    let hL : L.IsFiniteLocallyFree :=
      @Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank
        (toScheme.obj X) 1 L hLRank
    let EBundle : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree :
          ObjectProperty (toScheme.obj X).Modules) :=
      ⟨E, hE⟩
    let LBundle : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree :
          ObjectProperty (toScheme.obj X).Modules) :=
      ⟨L, hL⟩
    PowerSeries.coeff i
        (c.app X (ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.IsFiniteLocallyFree :
            ObjectProperty (toScheme.obj X).Modules)
          (Scheme.VectorBundleK0.tensorObj (toScheme.obj X) EBundle LBundle))) =
      ∑ j ∈ Finset.range (i + 1),
        (Nat.choose (r + j - i) j : A.obj (Opposite.op X)) *
          PowerSeries.coeff (i - j)
            (c.app X (ObjectProperty.GrothendieckGroup.of
              (SheafOfModules.IsFiniteLocallyFree :
                ObjectProperty (toScheme.obj X).Modules) EBundle)) *
          (S.firstChernClass X (Scheme.Modules.picardClass L) :
            A.obj (Opposite.op X)) ^ j := sorry

/-- A surjective coefficientwise realization of total Chern classes satisfies the binomial
formula for tensoring a finite locally free module by an invertible module, with the first
Chern class transported through the degree-one component equivalence. -/
theorem coeffTensorInvertibleOfRealization
    {C : Type u} [Category.{v} C] {toScheme : C ⥤ Scheme.{w}}
    {A : Cᵒᵖ ⥤ RingCat.{x}}
    {Agrade : ∀ X, ℕ → Submodule ℤ (A.obj (Opposite.op X))}
    [gradedAlgebra : ∀ X, GradedAlgebra (Agrade X)] (S : CohomologyTheory toScheme A Agrade)
    {B : C → ℕ → Type y} [∀ X i, AddCommGroup (B X i)]
    (componentEquiv : ∀ X i, Agrade X i ≃+ B X i)
    {R : Type z} (realize : TotalChernClass toScheme A Agrade S.firstChernClass → R)
    (realize_surjective : Function.Surjective realize)
    (app : R → ∀ X, Scheme.VectorBundleK0 (toScheme.obj X) → ∀ i, B X i)
    (app_spec : ∀ total X alpha,
      app (realize total) X alpha = fun i ↦
        componentEquiv X i ⟨PowerSeries.coeff i (total.app X alpha), total.coeff_mem X alpha i⟩)
    (firstChern : ∀ X, (toScheme.obj X).PicardGroup →+ B X 1)
    (firstChern_spec : ∀ X L,
      componentEquiv X 1 (S.firstChernClass X L) = firstChern X L)
    (c : R) (X : C)
    (E L : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules))
    (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r E.obj]
    [Scheme.Modules.Invertible L.obj] (i : ℕ) :
    ((componentEquiv X i).symm
        (app c X
          (ObjectProperty.GrothendieckGroup.of
            (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules)
            (Scheme.VectorBundleK0.tensorObj (toScheme.obj X) E L)) i) :
      A.obj (Opposite.op X)) =
      ∑ j ∈ Finset.range (i + 1),
        (Nat.choose (r + j - i) j : A.obj (Opposite.op X)) *
          ((componentEquiv X (i - j)).symm
              (app c X
                (ObjectProperty.GrothendieckGroup.of
                  (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules) E)
                (i - j)) : A.obj (Opposite.op X)) *
          ((componentEquiv X 1).symm
              (firstChern X (Scheme.Modules.picardClass L.obj)) : A.obj (Opposite.op X)) ^ j := sorry

end AlgebraicGeometry.ChernClass.TotalChernClass
