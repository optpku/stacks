module

public import ReasLib.AlgebraicGeometry.BivariantClass.Nonnegative.Basic
public import ReasLib.AlgebraicGeometry.BivariantClass.LocalizedExtension
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.TensorInvertible

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators DirectSum CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

open RingedSpace ModuleDerived

/-- For a perfect derived module of constant virtual rank zero on the second member of a closed
cover, tensoring by the pullback of an invertible module transforms the positive localized
Chern classes by the generalized binomial formula. -/
@[stacks 0FAN]
theorem localizedChernClass_tensor_invertible
    {S : Scheme.{u}} [UniversallyCatenary S] {delta : S → ℤ} [IsDimensionFunction delta]
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
    (i : ℕ) (positive : 0 < i) :
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
            (ChernClass.homogeneous delta X.hom 1 (classes.component L 1) ^ j)))) := sorry

end AlgebraicGeometry.LocalizedChern
