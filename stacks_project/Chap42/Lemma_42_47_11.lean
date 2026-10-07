module

public import stacks_project.Chap42.Lemma_42_46_11
public import stacks_project.Chap42.Lemma_42_47_1_LocalizedClass
public import stacks_project.Chap42.Lemma_42_47_11_IntersectionProduct
public import stacks_project.Chap42.Lemma_42_47_11_Pullback
public import stacks_project.Chap42.Remark_42_34_7_Cutoff
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Pullback

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

open ChernClass.Derived
open RingedSpace.ModuleDerived

section

variable {S : Scheme.{u}} [UniversallyCatenary S]
variable {δ : S → ℤ} [IsDimensionFunction δ]
variable {X : Over S} [LocallyOfFiniteType X.hom]
variable {X₁ X₂ X₁' X₂' W Y : Scheme.{u}}
variable (i₁ : X₁ ⟶ X.left) (i₂ : X₂ ⟶ X.left)
variable (i₁' : X₁' ⟶ X.left) (i₂' : X₂' ⟶ X.left)
variable (iY : Y ⟶ X.left) (iW : W ⟶ X.left)
variable [IsClosedImmersion i₁] [IsClosedImmersion i₂]
variable [IsClosedImmersion i₁'] [IsClosedImmersion i₂']
variable [IsClosedImmersion iY] [IsClosedImmersion iW]
variable (cover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
variable (cover' : Set.range i₁'.base ∪ Set.range i₂'.base = Set.univ)
variable (tensorCover : Set.range iY.base ∪ Set.range iW.base = Set.univ)
variable [KFlat.HomotopyTensorDescends X.left.toRingedSpace]
variable [KFlat.TensorDescends X.left.toRingedSpace]
variable [KFlat.IsLocalization X.left.toRingedSpace]
variable (E E' : RingedSpace.ModuleDerived X.left.toRingedSpace)
variable (perfect : RingedSpace.ModuleDerived.IsPerfect E)
variable (perfect' : RingedSpace.ModuleDerived.IsPerfect E')
variable (defined : ChernClass.Derived.IsDefined E)
variable (defined' : ChernClass.Derived.IsDefined E')
variable (restrictionZero : IsZero
  ((RingedSpace.modulePullbackDerived i₁.toShHom).obj E))
variable (restrictionZero' : IsZero
  ((RingedSpace.modulePullbackDerived i₁'.toShHom).obj E'))
variable (restrictionTensorZero : IsZero
  ((RingedSpace.modulePullbackDerived iY.toShHom).obj (E ⊗ᴸ E')))
variable (classes : ChernClass.Theory δ X.hom)
variable (j₂ : Over.mk (iW ≫ X.hom) ⟶ Over.mk (i₂ ≫ X.hom))
variable (j₂' : Over.mk (iW ≫ X.hom) ⟶ Over.mk (i₂' ≫ X.hom))
variable (square : IsPullback j₂.left j₂'.left i₂ i₂')
variable (intersection :
  j₂' ≫ (Over.homMk i₂' : Over.mk (i₂' ≫ X.hom) ⟶ X) =
    (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X))

include cover cover' tensorCover restrictionZero restrictionZero' restrictionTensorZero

/-- Lemma 42.47.11 (1): on the cartesian intersection of the two closed supports,
the first localized Chern class of `E ⊗ᴸ E'` is
`r * γ' 1 + γ 1 * r'`. -/
@[stacks 0FE5]
theorem localizedChernClass_tensor_one
    (r : BivariantClass δ
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) 0)
    (r' : BivariantClass δ
      (Over.homMk i₂' : Over.mk (i₂' ≫ X.hom) ⟶ X) 0)
    (γ : (p : ℕ) → BivariantClass δ
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) (p : ℤ))
    (γ' : (p : ℕ) → BivariantClass δ
      (Over.homMk i₂' : Over.mk (i₂' ≫ X.hom) ⟶ X) (p : ℤ))
    (tensorChern : (p : ℕ) → BivariantClass δ
      (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X) (p : ℤ))
    (r_spec : BivariantClass.IsLocalizedExtension δ X i₁ i₂ 0
      (ChernClass.Derived.rankClass δ (i₂ ≫ X.hom)
        ((RingedSpace.modulePullbackDerived i₂.toShHom).obj E)
        (RingedSpace.modulePullbackDerived_isPerfect i₂.toShHom E perfect)) r)
    (r'_spec : BivariantClass.IsLocalizedExtension δ X i₁' i₂' 0
      (ChernClass.Derived.rankClass δ (i₂' ≫ X.hom)
        ((RingedSpace.modulePullbackDerived i₂'.toShHom).obj E')
        (RingedSpace.modulePullbackDerived_isPerfect i₂'.toShHom E' perfect')) r')
    (γ_spec : ∀ p : ℕ, BivariantClass.IsLocalizedExtension δ X i₁ i₂ (p : ℤ)
      (ChernClass.Derived.totalClass δ (i₂ ≫ X.hom)
        (classes.reanchor (Over.mk (i₂ ≫ X.hom)))
        ((RingedSpace.modulePullbackDerived i₂.toShHom).obj E)
        (RingedSpace.modulePullbackDerived_isPerfect i₂.toShHom E perfect)
        (IsDefined.pullback i₂ defined) p) (γ p))
    (γ'_spec : ∀ p : ℕ, BivariantClass.IsLocalizedExtension δ X i₁' i₂' (p : ℤ)
      (ChernClass.Derived.totalClass δ (i₂' ≫ X.hom)
        (classes.reanchor (Over.mk (i₂' ≫ X.hom)))
        ((RingedSpace.modulePullbackDerived i₂'.toShHom).obj E')
        (RingedSpace.modulePullbackDerived_isPerfect i₂'.toShHom E' perfect')
        (IsDefined.pullback i₂' defined') p) (γ' p))
    (tensorChern_spec : ∀ p : ℕ,
      BivariantClass.IsLocalizedExtension δ X iY iW (p : ℤ)
        (ChernClass.Derived.totalClass δ (iW ≫ X.hom)
          (classes.reanchor (Over.mk (iW ≫ X.hom)))
          ((RingedSpace.modulePullbackDerived iW.toShHom).obj (E ⊗ᴸ E'))
          (RingedSpace.modulePullbackDerived_isPerfect iW.toShHom (E ⊗ᴸ E')
            (perfect.tensor perfect'))
          (IsDefined.pullback iW (defined.tensor defined')) p)
        (tensorChern p)) :
    tensorChern 1 =
      BivariantClass.Nonnegative.castGrading δ (zero_add (1 : ℤ))
        (BivariantClass.intersectionMul δ
          (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X)
          (Over.homMk i₂' : Over.mk (i₂' ≫ X.hom) ⟶ X)
          j₂ j₂' (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X)
          square intersection r (γ' 1)) +
        BivariantClass.Nonnegative.castGrading δ (add_zero (1 : ℤ))
          (BivariantClass.intersectionMul δ
          (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X)
          (Over.homMk i₂' : Over.mk (i₂' ≫ X.hom) ⟶ X)
          j₂ j₂' (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X)
          square intersection (γ 1) r') := sorry

/-- Lemma 42.47.11 (2): on the cartesian intersection of the two closed supports,
the second localized Chern class of `E ⊗ᴸ E'` has the five-term virtual-rank
expansion. -/
@[stacks 0FE5]
theorem localizedChernClass_tensor_two
    (r rChooseTwo : BivariantClass δ
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) 0)
    (r' rChooseTwo' : BivariantClass δ
      (Over.homMk i₂' : Over.mk (i₂' ≫ X.hom) ⟶ X) 0)
    (γ : (p : ℕ) → BivariantClass δ
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) (p : ℤ))
    (γ' : (p : ℕ) → BivariantClass δ
      (Over.homMk i₂' : Over.mk (i₂' ≫ X.hom) ⟶ X) (p : ℤ))
    (tensorChern : (p : ℕ) → BivariantClass δ
      (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X) (p : ℤ))
    (r_spec : BivariantClass.IsLocalizedExtension δ X i₁ i₂ 0
      (ChernClass.Derived.rankClass δ (i₂ ≫ X.hom)
        ((RingedSpace.modulePullbackDerived i₂.toShHom).obj E)
        (RingedSpace.modulePullbackDerived_isPerfect i₂.toShHom E perfect)) r)
    (r'_spec : BivariantClass.IsLocalizedExtension δ X i₁' i₂' 0
      (ChernClass.Derived.rankClass δ (i₂' ≫ X.hom)
        ((RingedSpace.modulePullbackDerived i₂'.toShHom).obj E')
        (RingedSpace.modulePullbackDerived_isPerfect i₂'.toShHom E' perfect')) r')
    (rChooseTwo_spec : BivariantClass.IsLocalizedExtension δ X i₁ i₂ 0
      (ChernClass.Derived.rankChoose δ (i₂ ≫ X.hom)
        ((RingedSpace.modulePullbackDerived i₂.toShHom).obj E)
        (RingedSpace.modulePullbackDerived_isPerfect i₂.toShHom E perfect) 2)
      rChooseTwo)
    (rChooseTwo'_spec : BivariantClass.IsLocalizedExtension δ X i₁' i₂' 0
      (ChernClass.Derived.rankChoose δ (i₂' ≫ X.hom)
        ((RingedSpace.modulePullbackDerived i₂'.toShHom).obj E')
        (RingedSpace.modulePullbackDerived_isPerfect i₂'.toShHom E' perfect') 2)
      rChooseTwo')
    (γ_spec : ∀ p : ℕ, BivariantClass.IsLocalizedExtension δ X i₁ i₂ (p : ℤ)
      (ChernClass.Derived.totalClass δ (i₂ ≫ X.hom)
        (classes.reanchor (Over.mk (i₂ ≫ X.hom)))
        ((RingedSpace.modulePullbackDerived i₂.toShHom).obj E)
        (RingedSpace.modulePullbackDerived_isPerfect i₂.toShHom E perfect)
        (IsDefined.pullback i₂ defined) p) (γ p))
    (γ'_spec : ∀ p : ℕ, BivariantClass.IsLocalizedExtension δ X i₁' i₂' (p : ℤ)
      (ChernClass.Derived.totalClass δ (i₂' ≫ X.hom)
        (classes.reanchor (Over.mk (i₂' ≫ X.hom)))
        ((RingedSpace.modulePullbackDerived i₂'.toShHom).obj E')
        (RingedSpace.modulePullbackDerived_isPerfect i₂'.toShHom E' perfect')
        (IsDefined.pullback i₂' defined') p) (γ' p))
    (tensorChern_spec : ∀ p : ℕ,
      BivariantClass.IsLocalizedExtension δ X iY iW (p : ℤ)
        (ChernClass.Derived.totalClass δ (iW ≫ X.hom)
          (classes.reanchor (Over.mk (iW ≫ X.hom)))
          ((RingedSpace.modulePullbackDerived iW.toShHom).obj (E ⊗ᴸ E'))
          (RingedSpace.modulePullbackDerived_isPerfect iW.toShHom (E ⊗ᴸ E')
            (perfect.tensor perfect'))
          (IsDefined.pullback iW (defined.tensor defined')) p)
        (tensorChern p)) :
    tensorChern 2 =
      BivariantClass.Nonnegative.castGrading δ (zero_add (2 : ℤ))
        (BivariantClass.intersectionMul δ
          (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X)
          (Over.homMk i₂' : Over.mk (i₂' ≫ X.hom) ⟶ X)
          j₂ j₂' (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X)
          square intersection r (γ' 2)) +
        BivariantClass.Nonnegative.castGrading δ (add_zero (2 : ℤ))
          (BivariantClass.intersectionMul δ
          (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X)
          (Over.homMk i₂' : Over.mk (i₂' ≫ X.hom) ⟶ X)
          j₂ j₂' (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X)
          square intersection (γ 2) r') +
        BivariantClass.Nonnegative.castGrading δ (Nat.cast_add 0 2).symm
          (BivariantClass.intersectionMul δ
            (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X)
            (Over.homMk i₂' : Over.mk (i₂' ≫ X.hom) ⟶ X)
            j₂ j₂' (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X)
            square intersection rChooseTwo
            (BivariantClass.Nonnegative.castGrading δ (Nat.cast_add 1 1).symm
              (BivariantClass.Cutoff.relativeMul δ
                (Over.homMk i₂' : Over.mk (i₂' ≫ X.hom) ⟶ X) 1 1
                (γ' 1) (γ' 1)))) +
        (BivariantClass.Nonnegative.castGrading δ (Nat.cast_add 1 1).symm
            (BivariantClass.intersectionMul δ
              (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X)
              (Over.homMk i₂' : Over.mk (i₂' ≫ X.hom) ⟶ X)
              j₂ j₂' (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X)
              square intersection
              (BivariantClass.Nonnegative.castGrading δ (Nat.cast_add 0 1).symm
                (BivariantClass.Cutoff.relativeMul δ
                  (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X)
                  0 1 r (γ 1)))
              (BivariantClass.Nonnegative.castGrading δ (Nat.cast_add 0 1).symm
                (BivariantClass.Cutoff.relativeMul δ
                  (Over.homMk i₂' : Over.mk (i₂' ≫ X.hom) ⟶ X)
                  0 1 r' (γ' 1)))) -
          BivariantClass.Nonnegative.castGrading δ (Nat.cast_add 1 1).symm
            (BivariantClass.intersectionMul δ
              (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X)
              (Over.homMk i₂' : Over.mk (i₂' ≫ X.hom) ⟶ X)
              j₂ j₂' (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X)
              square intersection (γ 1) (γ' 1))) +
        BivariantClass.Nonnegative.castGrading δ (Nat.cast_add 2 0).symm
          (BivariantClass.intersectionMul δ
            (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X)
            (Over.homMk i₂' : Over.mk (i₂' ≫ X.hom) ⟶ X)
            j₂ j₂' (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X)
            square intersection
            (BivariantClass.Nonnegative.castGrading δ (Nat.cast_add 1 1).symm
              (BivariantClass.Cutoff.relativeMul δ
                (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X)
                1 1 (γ 1) (γ 1)))
            rChooseTwo') := sorry

/-- Lemma 42.47.11 (3): every localized Newton class of `E ⊗ᴸ E'` is the
binomial antidiagonal convolution of the localized Newton classes of `E` and `E'`. -/
@[stacks 0FE5]
theorem localizedNewtonClass_tensor
    (χ : (p : ℕ) → BivariantClass δ
      (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X) (p : ℤ))
    (χ' : (p : ℕ) → BivariantClass δ
      (Over.homMk i₂' : Over.mk (i₂' ≫ X.hom) ⟶ X) (p : ℤ))
    (tensorNewton : (p : ℕ) → BivariantClass δ
      (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X) (p : ℤ))
    (χ_spec : ∀ p : ℕ, BivariantClass.IsLocalizedExtension δ X i₁ i₂ (p : ℤ)
      (ChernClass.Derived.newtonClass δ (i₂ ≫ X.hom)
        (classes.reanchor (Over.mk (i₂ ≫ X.hom)))
        ((RingedSpace.modulePullbackDerived i₂.toShHom).obj E)
        (RingedSpace.modulePullbackDerived_isPerfect i₂.toShHom E perfect)
        (IsDefined.pullback i₂ defined) p) (χ p))
    (χ'_spec : ∀ p : ℕ, BivariantClass.IsLocalizedExtension δ X i₁' i₂' (p : ℤ)
      (ChernClass.Derived.newtonClass δ (i₂' ≫ X.hom)
        (classes.reanchor (Over.mk (i₂' ≫ X.hom)))
        ((RingedSpace.modulePullbackDerived i₂'.toShHom).obj E')
        (RingedSpace.modulePullbackDerived_isPerfect i₂'.toShHom E' perfect')
        (IsDefined.pullback i₂' defined') p) (χ' p))
    (tensorNewton_spec : ∀ p : ℕ,
      BivariantClass.IsLocalizedExtension δ X iY iW (p : ℤ)
        (ChernClass.Derived.newtonClass δ (iW ≫ X.hom)
          (classes.reanchor (Over.mk (iW ≫ X.hom)))
          ((RingedSpace.modulePullbackDerived iW.toShHom).obj (E ⊗ᴸ E'))
          (RingedSpace.modulePullbackDerived_isPerfect iW.toShHom (E ⊗ᴸ E')
            (perfect.tensor perfect'))
          (IsDefined.pullback iW (defined.tensor defined')) p)
        (tensorNewton p))
    (p : ℕ) :
    tensorNewton p =
      ∑ ij : Finset.antidiagonal p, p.choose ij.1.1 •
        BivariantClass.Nonnegative.castGrading δ
          (BivariantClass.Nonnegative.antidiagonalDegree p ij)
          (BivariantClass.intersectionMul δ
            (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X)
            (Over.homMk i₂' : Over.mk (i₂' ≫ X.hom) ⟶ X)
            j₂ j₂' (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X)
            square intersection (χ ij.1.1) (χ' ij.1.2)) := sorry

end

end AlgebraicGeometry.LocalizedChern
