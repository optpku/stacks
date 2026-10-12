/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChernClass.Tensor
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped BigOperators

noncomputable section

universe u v w x

/- Lemma 45.12.3: if `E` is finite locally free of constant rank `r` and `L` is
invertible, then the `i`-th Chern class of `E ⊗ L` is the binomial sum of the
Chern classes of `E` and powers of the first Chern class of `L`. -/
@[stacks 0FI8] #check
  (AlgebraicGeometry.ChernClass.TotalChernClass.coeff_tensor_invertible :
    ∀ {C : Type u} [Category.{v} C]
      (toScheme : C ⥤ AlgebraicGeometry.Scheme.{w})
      (A : Cᵒᵖ ⥤ RingCat.{x})
      (Agrade : ∀ X, ℕ → Submodule ℤ (A.obj (Opposite.op X)))
      [∀ X, GradedAlgebra (Agrade X)]
      (S : AlgebraicGeometry.ChernClass.Theory toScheme A Agrade)
      (c : AlgebraicGeometry.ChernClass.TotalChernClass
        toScheme A Agrade S.firstChernClass)
      (X : C) (E L : (toScheme.obj X).Modules) (r i : ℕ)
      [AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
      [AlgebraicGeometry.Scheme.Modules.Invertible L],
      let hE : E.IsFiniteLocallyFree :=
        AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank r E
      let hLRank : L.IsFiniteLocallyFreeOfRank 1 :=
        AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRankOne_of_invertible L
      let hL : L.IsFiniteLocallyFree :=
        @AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank
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
            (AlgebraicGeometry.Scheme.VectorBundleK0.tensorObj
              (toScheme.obj X) EBundle LBundle))) =
        ∑ j ∈ Finset.range (i + 1),
          (Nat.choose (r + j - i) j : A.obj (Opposite.op X)) *
            PowerSeries.coeff (i - j)
              (c.app X (ObjectProperty.GrothendieckGroup.of
                (SheafOfModules.IsFiniteLocallyFree :
                  ObjectProperty (toScheme.obj X).Modules) EBundle)) *
            (S.firstChernClass X (AlgebraicGeometry.Scheme.Modules.picardClass L) :
              A.obj (Opposite.op X)) ^ j)
