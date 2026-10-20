/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.LocalizedChern.ClosedCover.TensorInvertible

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators DirectSum CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

open RingedSpace ModuleDerived

/- Lemma 42.47.10: the positive localized Chern classes of an invertible twist satisfy the
 generalized binomial formula. The localization specifications express their agreement and
 vanishing cap laws on the closed cover. The endpoint j = i is omitted because its coefficient
 is binom(0,i) = 0 for positive i, as expressed by Ring.choose_zero_pos. -/
@[stacks 0FAN] #check (AlgebraicGeometry.LocalizedChern.localizedChernClass_tensor_invertible :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] {delta : S → ℤ} [IsDimensionFunction delta]
    {X : Over S} [LocallyOfFiniteType X.hom]
    {X₁ X₂ : Scheme.{u}} (i₁ : X₁ ⟶ X.left) (i₂ : X₂ ⟶ X.left)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (cover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    [KFlat.HomotopyTensorDescends X₂.toRingedSpace]
    [KFlat.TensorDescends X₂.toRingedSpace]
    [KFlat.IsLocalization X₂.toRingedSpace]
    (E₂ : RingedSpace.ModuleDerived X₂.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E₂)
    (defined : ChernClass.Derived.IsDefined E₂)
    (rankZero : Scheme.ModuleDerived.IsConstantRank E₂ 0)
    (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (classes : ChernClass.Theory delta X.hom)
    (localizedClass : RingedSpace.ModuleDerived X₂.toRingedSpace → (q : ℕ) →
      BivariantClass delta (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) (q : ℤ))
    (localizedClass_spec : ∀ (q : ℕ), 0 < q →
      BivariantClass.IsLocalizedExtension delta X i₁ i₂ (q : ℤ)
        (ChernClass.Derived.totalClass delta (i₂ ≫ X.hom)
          (classes.reanchor (Over.mk (i₂ ≫ X.hom))) E₂ perfect defined q)
        (localizedClass E₂ q))
    (localizedTensorClass_spec : ∀ (q : ℕ), 0 < q →
      BivariantClass.IsLocalizedExtension delta X i₁ i₂ (q : ℤ)
        (ChernClass.Derived.totalClass delta (i₂ ≫ X.hom)
          (classes.reanchor (Over.mk (i₂ ≫ X.hom)))
          (E₂ ⊗ᴸ (DerivedCategory.singleFunctor X₂.toRingedSpace.Modules (0 : ℤ)).obj
            ((Scheme.Modules.pullback i₂).obj L))
          (perfect.tensorInvertible ((Scheme.Modules.pullback i₂).obj L))
          (defined.tensorInvertible ((Scheme.Modules.pullback i₂).obj L)) q)
        (localizedClass
          (E₂ ⊗ᴸ (DerivedCategory.singleFunctor X₂.toRingedSpace.Modules (0 : ℤ)).obj
            ((Scheme.Modules.pullback i₂).obj L)) q))
    (i : ℕ) (positive : 0 < i),
    BivariantClass.Nonnegative.single delta
        (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) i
        (localizedClass
          (E₂ ⊗ᴸ (DerivedCategory.singleFunctor X₂.toRingedSpace.Modules (0 : ℤ)).obj
            ((Scheme.Modules.pullback i₂).obj L)) i) =
      BivariantClass.Nonnegative.sum delta
        (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) (Finset.range i) (fun j ↦
        BivariantClass.Nonnegative.zsmul delta
          (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X)
          (Ring.choose (-(i : ℤ) + (j : ℤ)) j : ℤ)
          (BivariantClass.Nonnegative.castHom delta
          (Category.comp_id (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X))
          (BivariantClass.Nonnegative.comp delta
            (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) (𝟙 X)
            (BivariantClass.Nonnegative.single delta
              (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) (i - j)
              (localizedClass E₂ (i - j)))
            (ChernClass.homogeneous delta X.hom 1 (classes.component L 1) ^ j)))))

end AlgebraicGeometry.LocalizedChern
