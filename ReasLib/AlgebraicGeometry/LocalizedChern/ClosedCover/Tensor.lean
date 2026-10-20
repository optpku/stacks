/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Intersection
public import ReasLib.AlgebraicGeometry.BivariantClass.FiniteSum
public import ReasLib.AlgebraicGeometry.BivariantClass.LocalizedExtension
public import ReasLib.AlgebraicGeometry.BivariantClass.Cutoff.Basic
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.Tensor
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Pullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/-- The closed union of two subschemes, defined by the product of their kernel ideals. -/
@[reducible]
def tensorZeroLocus {X X₁ X₁' : Scheme.{u}}
    (i₁ : X₁ ⟶ X) (i₁' : X₁' ⟶ X) : Scheme.{u} :=
  (i₁.ker * i₁'.ker).subscheme

/-- The canonical closed immersion of the union defined by the product of kernel ideals. -/
@[reducible]
def tensorZeroLocusι {X X₁ X₁' : Scheme.{u}}
    (i₁ : X₁ ⟶ X) (i₁' : X₁' ⟶ X) : tensorZeroLocus i₁ i₁' ⟶ X :=
  (i₁.ker * i₁'.ker).subschemeι

/-- The union immersion has range equal to the union of the two closed ranges. -/
theorem tensorZeroLocus_range {X X₁ X₁' : Scheme.{u}}
    (i₁ : X₁ ⟶ X) (i₁' : X₁' ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₁'] :
    Set.range (tensorZeroLocusι i₁ i₁').base =
      Set.range i₁.base ∪ Set.range i₁'.base := sorry

/-- Two closed covers induce a cover by the union of their first members and the
cartesian intersection of their second members. -/
theorem tensorZeroLocus_cover {X X₁ X₂ X₁' X₂' W : Scheme.{u}}
    (i₁ : X₁ ⟶ X) (i₂ : X₂ ⟶ X) (i₁' : X₁' ⟶ X) (i₂' : X₂' ⟶ X)
    (iW : W ⟶ X) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    [IsClosedImmersion i₁'] [IsClosedImmersion i₂'] [IsClosedImmersion iW]
    (cover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (cover' : Set.range i₁'.base ∪ Set.range i₂'.base = Set.univ)
    (j₂ : W ⟶ X₂) (j₂' : W ⟶ X₂')
    (square : IsPullback j₂ j₂' i₂ i₂') (intersection : j₂' ≫ i₂' = iW) :
    Set.range (tensorZeroLocusι i₁ i₁').base ∪ Set.range iW.base = Set.univ := sorry

/-- A derived tensor product of perfect objects vanishes on the closed union of
subschemes where the respective factors vanish. -/
theorem tensor_restrictionZero {X X₁ X₁' : Scheme.{u}}
    (i₁ : X₁ ⟶ X) (i₁' : X₁' ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₁']
    (E E' : RingedSpace.ModuleDerived X.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (perfect' : RingedSpace.ModuleDerived.IsPerfect E')
    (restrictionZero : IsZero ((RingedSpace.modulePullbackDerived i₁.toShHom).obj E))
    (restrictionZero' : IsZero ((RingedSpace.modulePullbackDerived i₁'.toShHom).obj E')) :
    IsZero ((RingedSpace.modulePullbackDerived (tensorZeroLocusι i₁ i₁').toShHom).obj
      (E ⊗ᴸ E')) := sorry

open ChernClass.Derived
open RingedSpace.ModuleDerived

section

variable {S : Scheme.{u}} [UniversallyCatenary S]
variable {δ : S → ℤ} [IsDimensionFunction δ]
variable {X : Over S} [LocallyOfFiniteType X.hom]
variable {X₁ X₂ X₁' X₂' W : Scheme.{u}}
variable (i₁ : X₁ ⟶ X.left) (i₂ : X₂ ⟶ X.left)
variable (i₁' : X₁' ⟶ X.left) (i₂' : X₂' ⟶ X.left)
variable (iW : W ⟶ X.left)
variable [IsClosedImmersion i₁] [IsClosedImmersion i₂]
variable [IsClosedImmersion i₁'] [IsClosedImmersion i₂']
variable [IsClosedImmersion iW]
variable (cover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
variable (cover' : Set.range i₁'.base ∪ Set.range i₂'.base = Set.univ)
variable (E E' : RingedSpace.ModuleDerived X.left.toRingedSpace)
variable (perfect : RingedSpace.ModuleDerived.IsPerfect E)
variable (perfect' : RingedSpace.ModuleDerived.IsPerfect E')
variable (defined : ChernClass.Derived.IsDefined E)
variable (defined' : ChernClass.Derived.IsDefined E')
variable (restrictionZero : IsZero
  ((RingedSpace.modulePullbackDerived i₁.toShHom).obj E))
variable (restrictionZero' : IsZero
  ((RingedSpace.modulePullbackDerived i₁'.toShHom).obj E'))
variable (classes : ChernClass.Theory δ X.hom)
variable (j₂ : Over.mk (iW ≫ X.hom) ⟶ Over.mk (i₂ ≫ X.hom))
variable (j₂' : Over.mk (iW ≫ X.hom) ⟶ Over.mk (i₂' ≫ X.hom))
variable (square : IsPullback j₂.left j₂'.left i₂ i₂')
variable (intersection :
  j₂' ≫ (Over.homMk i₂' : Over.mk (i₂' ≫ X.hom) ⟶ X) =
    (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X))

include cover cover' restrictionZero restrictionZero'

/-- On the cartesian intersection of two closed supports,
the first localized Chern class of `E ⊗ᴸ E'` is
`r * γ' 1 + γ 1 * r'`. -/
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
    (γ_spec : ∀ p : ℕ, 0 < p → BivariantClass.IsLocalizedExtension δ X i₁ i₂ (p : ℤ)
      (ChernClass.Derived.totalClass δ (i₂ ≫ X.hom)
        (classes.reanchor (Over.mk (i₂ ≫ X.hom)))
        ((RingedSpace.modulePullbackDerived i₂.toShHom).obj E)
        (RingedSpace.modulePullbackDerived_isPerfect i₂.toShHom E perfect)
        (IsDefined.pullback i₂ defined) p) (γ p))
    (γ'_spec : ∀ p : ℕ, 0 < p → BivariantClass.IsLocalizedExtension δ X i₁' i₂' (p : ℤ)
      (ChernClass.Derived.totalClass δ (i₂' ≫ X.hom)
        (classes.reanchor (Over.mk (i₂' ≫ X.hom)))
        ((RingedSpace.modulePullbackDerived i₂'.toShHom).obj E')
        (RingedSpace.modulePullbackDerived_isPerfect i₂'.toShHom E' perfect')
        (IsDefined.pullback i₂' defined') p) (γ' p))
    (tensorChern_spec : ∀ p : ℕ, 0 < p →
      BivariantClass.IsLocalizedExtension δ X (tensorZeroLocusι i₁ i₁') iW (p : ℤ)
        (ChernClass.Derived.totalClass δ (iW ≫ X.hom)
          (classes.reanchor (Over.mk (iW ≫ X.hom)))
          ((RingedSpace.modulePullbackDerived iW.toShHom).obj (E ⊗ᴸ E'))
          (RingedSpace.modulePullbackDerived_isPerfect iW.toShHom (E ⊗ᴸ E')
            (RingedSpace.ModuleDerived.IsPerfect.tensor perfect perfect'))
          (IsDefined.pullback iW (defined.derivedTensor defined')) p)
        (tensorChern p)) :
    tensorChern 1 =
    BivariantClass.pointwiseAdd δ
      (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X) 1
      (BivariantClass.Nonnegative.castGrading δ (zero_add (1 : ℤ))
        (BivariantClass.intersectionMul δ
          (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X)
          (Over.homMk i₂' : Over.mk (i₂' ≫ X.hom) ⟶ X)
          j₂ j₂' (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X)
          square intersection r (γ' 1)))
      (BivariantClass.Nonnegative.castGrading δ (add_zero (1 : ℤ))
          (BivariantClass.intersectionMul δ
          (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X)
          (Over.homMk i₂' : Over.mk (i₂' ≫ X.hom) ⟶ X)
          j₂ j₂' (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X)
          square intersection (γ 1) r')) := sorry

/-- On the cartesian intersection of two closed supports,
the second localized Chern class of `E ⊗ᴸ E'` has the five-term virtual-rank
expansion. -/
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
    (γ_spec : ∀ p : ℕ, 0 < p → BivariantClass.IsLocalizedExtension δ X i₁ i₂ (p : ℤ)
      (ChernClass.Derived.totalClass δ (i₂ ≫ X.hom)
        (classes.reanchor (Over.mk (i₂ ≫ X.hom)))
        ((RingedSpace.modulePullbackDerived i₂.toShHom).obj E)
        (RingedSpace.modulePullbackDerived_isPerfect i₂.toShHom E perfect)
        (IsDefined.pullback i₂ defined) p) (γ p))
    (γ'_spec : ∀ p : ℕ, 0 < p → BivariantClass.IsLocalizedExtension δ X i₁' i₂' (p : ℤ)
      (ChernClass.Derived.totalClass δ (i₂' ≫ X.hom)
        (classes.reanchor (Over.mk (i₂' ≫ X.hom)))
        ((RingedSpace.modulePullbackDerived i₂'.toShHom).obj E')
        (RingedSpace.modulePullbackDerived_isPerfect i₂'.toShHom E' perfect')
        (IsDefined.pullback i₂' defined') p) (γ' p))
    (tensorChern_spec : ∀ p : ℕ, 0 < p →
      BivariantClass.IsLocalizedExtension δ X (tensorZeroLocusι i₁ i₁') iW (p : ℤ)
        (ChernClass.Derived.totalClass δ (iW ≫ X.hom)
          (classes.reanchor (Over.mk (iW ≫ X.hom)))
          ((RingedSpace.modulePullbackDerived iW.toShHom).obj (E ⊗ᴸ E'))
          (RingedSpace.modulePullbackDerived_isPerfect iW.toShHom (E ⊗ᴸ E')
            (RingedSpace.ModuleDerived.IsPerfect.tensor perfect perfect'))
          (IsDefined.pullback iW (defined.derivedTensor defined')) p)
        (tensorChern p)) :
    tensorChern 2 =
    BivariantClass.pointwiseAdd δ
      (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X) 2
      (BivariantClass.pointwiseAdd δ
      (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X) 2
      (BivariantClass.pointwiseAdd δ
      (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X) 2
      (BivariantClass.pointwiseAdd δ
      (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X) 2
      (BivariantClass.Nonnegative.castGrading δ (zero_add (2 : ℤ))
        (BivariantClass.intersectionMul δ
          (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X)
          (Over.homMk i₂' : Over.mk (i₂' ≫ X.hom) ⟶ X)
          j₂ j₂' (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X)
          square intersection r (γ' 2)))
      (BivariantClass.Nonnegative.castGrading δ (add_zero (2 : ℤ))
          (BivariantClass.intersectionMul δ
          (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X)
          (Over.homMk i₂' : Over.mk (i₂' ≫ X.hom) ⟶ X)
          j₂ j₂' (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X)
          square intersection (γ 2) r')))
      (BivariantClass.Nonnegative.castGrading δ (Nat.cast_add 0 2).symm
          (BivariantClass.intersectionMul δ
            (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X)
            (Over.homMk i₂' : Over.mk (i₂' ≫ X.hom) ⟶ X)
            j₂ j₂' (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X)
            square intersection rChooseTwo
            (BivariantClass.Nonnegative.castGrading δ (Nat.cast_add 1 1).symm
              (BivariantClass.Cutoff.relativeMul δ
                (Over.homMk i₂' : Over.mk (i₂' ≫ X.hom) ⟶ X) 1 1
                (γ' 1) (γ' 1))))))
      (BivariantClass.pointwiseAdd δ
      (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X) 2
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
                  0 1 r' (γ' 1)))))
      (BivariantClass.pointwiseNeg δ
      (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X) 2 (BivariantClass.Nonnegative.castGrading δ (Nat.cast_add 1 1).symm
            (BivariantClass.intersectionMul δ
              (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X)
              (Over.homMk i₂' : Over.mk (i₂' ≫ X.hom) ⟶ X)
              j₂ j₂' (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X)
              square intersection (γ 1) (γ' 1))))))
      (BivariantClass.Nonnegative.castGrading δ (Nat.cast_add 2 0).symm
          (BivariantClass.intersectionMul δ
            (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X)
            (Over.homMk i₂' : Over.mk (i₂' ≫ X.hom) ⟶ X)
            j₂ j₂' (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X)
            square intersection
            (BivariantClass.Nonnegative.castGrading δ (Nat.cast_add 1 1).symm
              (BivariantClass.Cutoff.relativeMul δ
                (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X)
                1 1 (γ 1) (γ 1)))
            rChooseTwo')) := sorry

/-- Every localized Newton class of `E ⊗ᴸ E'` is the
binomial antidiagonal convolution of the localized Newton classes of `E` and `E'`. -/
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
      BivariantClass.IsLocalizedExtension δ X (tensorZeroLocusι i₁ i₁') iW (p : ℤ)
        (ChernClass.Derived.newtonClass δ (iW ≫ X.hom)
          (classes.reanchor (Over.mk (iW ≫ X.hom)))
          ((RingedSpace.modulePullbackDerived iW.toShHom).obj (E ⊗ᴸ E'))
          (RingedSpace.modulePullbackDerived_isPerfect iW.toShHom (E ⊗ᴸ E')
            (RingedSpace.ModuleDerived.IsPerfect.tensor perfect perfect'))
          (IsDefined.pullback iW (defined.derivedTensor defined')) p)
        (tensorNewton p))
    (p : ℕ) :
    tensorNewton p =
      BivariantClass.pointwiseSum δ
        (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X) (p : ℤ)
        (Finset.univ : Finset (Finset.antidiagonal p)) (fun ij ↦
          BivariantClass.pointwiseNsmul δ
            (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X) (p : ℤ)
            (BivariantClass.Nonnegative.castGrading δ
          (BivariantClass.Nonnegative.antidiagonalDegree p ij)
          (BivariantClass.intersectionMul δ
            (Over.homMk i₂ : Over.mk (i₂ ≫ X.hom) ⟶ X)
            (Over.homMk i₂' : Over.mk (i₂' ≫ X.hom) ⟶ X)
            j₂ j₂' (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X)
            square intersection (χ ij.1.1) (χ' ij.1.2))) (p.choose ij.1.1)) := sorry

end

end AlgebraicGeometry.LocalizedChern

