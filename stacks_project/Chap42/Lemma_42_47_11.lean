module

public import ReasLib.AlgebraicGeometry.LocalizedChern.ClosedCover.Tensor
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

open ChernClass.Derived
open RingedSpace.ModuleDerived

/- Lemma 42.47.11 (1): localized derived tensor identity. -/
@[stacks 0FE5] #check (AlgebraicGeometry.LocalizedChern.localizedChernClass_tensor_one :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S]
    {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom]
    {X₁ X₂ X₁' X₂' W : Scheme.{u}}
    (i₁ : X₁ ⟶ X.left) (i₂ : X₂ ⟶ X.left)
    (i₁' : X₁' ⟶ X.left) (i₂' : X₂' ⟶ X.left)
    (iW : W ⟶ X.left)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    [IsClosedImmersion i₁'] [IsClosedImmersion i₂']
    [IsClosedImmersion iW]
    (cover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (cover' : Set.range i₁'.base ∪ Set.range i₂'.base = Set.univ)
    (E E' : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (perfect' : RingedSpace.ModuleDerived.IsPerfect E')
    (defined : ChernClass.Derived.IsDefined E)
    (defined' : ChernClass.Derived.IsDefined E')
    (restrictionZero : IsZero
      ((RingedSpace.modulePullbackDerived i₁.toShHom).obj E))
    (restrictionZero' : IsZero
      ((RingedSpace.modulePullbackDerived i₁'.toShHom).obj E'))
    (classes : ChernClass.Theory δ X.hom)
    (j₂ : Over.mk (iW ≫ X.hom) ⟶ Over.mk (i₂ ≫ X.hom))
    (j₂' : Over.mk (iW ≫ X.hom) ⟶ Over.mk (i₂' ≫ X.hom))
    (square : IsPullback j₂.left j₂'.left i₂ i₂')
    (intersection :
      j₂' ≫ (Over.homMk i₂' : Over.mk (i₂' ≫ X.hom) ⟶ X) =
        (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X)),
  ∀ (r : BivariantClass δ
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
        (tensorChern p)),
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
          square intersection (γ 1) r')))

/- Lemma 42.47.11 (2): localized derived tensor identity. -/
@[stacks 0FE5] #check (AlgebraicGeometry.LocalizedChern.localizedChernClass_tensor_two :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S]
    {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom]
    {X₁ X₂ X₁' X₂' W : Scheme.{u}}
    (i₁ : X₁ ⟶ X.left) (i₂ : X₂ ⟶ X.left)
    (i₁' : X₁' ⟶ X.left) (i₂' : X₂' ⟶ X.left)
    (iW : W ⟶ X.left)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    [IsClosedImmersion i₁'] [IsClosedImmersion i₂']
    [IsClosedImmersion iW]
    (cover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (cover' : Set.range i₁'.base ∪ Set.range i₂'.base = Set.univ)
    (E E' : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (perfect' : RingedSpace.ModuleDerived.IsPerfect E')
    (defined : ChernClass.Derived.IsDefined E)
    (defined' : ChernClass.Derived.IsDefined E')
    (restrictionZero : IsZero
      ((RingedSpace.modulePullbackDerived i₁.toShHom).obj E))
    (restrictionZero' : IsZero
      ((RingedSpace.modulePullbackDerived i₁'.toShHom).obj E'))
    (classes : ChernClass.Theory δ X.hom)
    (j₂ : Over.mk (iW ≫ X.hom) ⟶ Over.mk (i₂ ≫ X.hom))
    (j₂' : Over.mk (iW ≫ X.hom) ⟶ Over.mk (i₂' ≫ X.hom))
    (square : IsPullback j₂.left j₂'.left i₂ i₂')
    (intersection :
      j₂' ≫ (Over.homMk i₂' : Over.mk (i₂' ≫ X.hom) ⟶ X) =
        (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X)),
  ∀ (r rChooseTwo : BivariantClass δ
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
        (tensorChern p)),
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
                (Over.homMk i₂' rfl : Over.mk (i₂' ≫ X.hom) ⟶ X) 1 1
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
                  (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X)
                  0 1 r (γ 1)))
              (BivariantClass.Nonnegative.castGrading δ (Nat.cast_add 0 1).symm
                (BivariantClass.Cutoff.relativeMul δ
                  (Over.homMk i₂' rfl : Over.mk (i₂' ≫ X.hom) ⟶ X)
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
                (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X)
                1 1 (γ 1) (γ 1)))
            rChooseTwo')))

/- Lemma 42.47.11 (3): localized derived tensor identity. -/
@[stacks 0FE5] #check (AlgebraicGeometry.LocalizedChern.localizedNewtonClass_tensor :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S]
    {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom]
    {X₁ X₂ X₁' X₂' W : Scheme.{u}}
    (i₁ : X₁ ⟶ X.left) (i₂ : X₂ ⟶ X.left)
    (i₁' : X₁' ⟶ X.left) (i₂' : X₂' ⟶ X.left)
    (iW : W ⟶ X.left)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    [IsClosedImmersion i₁'] [IsClosedImmersion i₂']
    [IsClosedImmersion iW]
    (cover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (cover' : Set.range i₁'.base ∪ Set.range i₂'.base = Set.univ)
    (E E' : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (perfect' : RingedSpace.ModuleDerived.IsPerfect E')
    (defined : ChernClass.Derived.IsDefined E)
    (defined' : ChernClass.Derived.IsDefined E')
    (restrictionZero : IsZero
      ((RingedSpace.modulePullbackDerived i₁.toShHom).obj E))
    (restrictionZero' : IsZero
      ((RingedSpace.modulePullbackDerived i₁'.toShHom).obj E'))
    (classes : ChernClass.Theory δ X.hom)
    (j₂ : Over.mk (iW ≫ X.hom) ⟶ Over.mk (i₂ ≫ X.hom))
    (j₂' : Over.mk (iW ≫ X.hom) ⟶ Over.mk (i₂' ≫ X.hom))
    (square : IsPullback j₂.left j₂'.left i₂ i₂')
    (intersection :
      j₂' ≫ (Over.homMk i₂' : Over.mk (i₂' ≫ X.hom) ⟶ X) =
        (Over.homMk iW : Over.mk (iW ≫ X.hom) ⟶ X)),
  ∀ (χ : (p : ℕ) → BivariantClass δ
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
    (p : ℕ),
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
            square intersection (χ ij.1.1) (χ' ij.1.2))) (p.choose ij.1.1)))

end AlgebraicGeometry.LocalizedChern
