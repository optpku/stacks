module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.LocalizedChern.ClosedCover.Newton

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/- Lemma 42.47.7 (1): The first localized Newton class of a perfect complex vanishing on the intersection
of a two-member closed cover equals its first localized Chern class. -/
@[stacks 0FAK]
#check (AlgebraicGeometry.LocalizedChern.localizedNewtonClass_one :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S]
    {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom]
    {X₁ X₂ : Scheme.{u}}
    (i₁ : X₁ ⟶ X.left) (i₂ : X₂ ⟶ X.left)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (cover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (E₂ : RingedSpace.ModuleDerived X₂.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E₂)
    (defined : ChernClass.Derived.IsDefined E₂)
    (restrictionZero : IsZero
      ((RingedSpace.modulePullbackDerived (pullback.snd i₁ i₂).toShHom).obj E₂))
    (classes : ChernClass.Theory δ X.hom)
    (localizedNewton localizedChern :
      (p : ℕ) → BivariantClass δ
        (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) (p : ℤ))
    (localizedNewton_spec : ∀ p : ℕ, 0 < p →
      BivariantClass.IsLocalizedExtension δ X i₁ i₂ (p : ℤ)
        (ChernClass.Derived.newtonClass δ (i₂ ≫ X.hom)
          (classes.reanchor (Over.mk (i₂ ≫ X.hom))) E₂ perfect defined p)
        (localizedNewton p))
    (localizedChern_spec : ∀ p : ℕ, 0 < p →
      BivariantClass.IsLocalizedExtension δ X i₁ i₂ (p : ℤ)
        (ChernClass.Derived.totalClass δ (i₂ ≫ X.hom)
          (classes.reanchor (Over.mk (i₂ ≫ X.hom))) E₂ perfect defined p)
        (localizedChern p)),
    localizedNewton 1 =
      (localizedChern 1))

/- Lemma 42.47.7 (2): The second localized Newton class of a perfect complex vanishing on the intersection
of a two-member closed cover is `c₁² - 2c₂`, with relative multiplication. -/
@[stacks 0FAK]
#check (AlgebraicGeometry.LocalizedChern.localizedNewtonClass_two :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S]
    {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom]
    {X₁ X₂ : Scheme.{u}}
    (i₁ : X₁ ⟶ X.left) (i₂ : X₂ ⟶ X.left)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (cover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (E₂ : RingedSpace.ModuleDerived X₂.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E₂)
    (defined : ChernClass.Derived.IsDefined E₂)
    (restrictionZero : IsZero
      ((RingedSpace.modulePullbackDerived (pullback.snd i₁ i₂).toShHom).obj E₂))
    (classes : ChernClass.Theory δ X.hom)
    (localizedNewton localizedChern :
      (p : ℕ) → BivariantClass δ
        (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) (p : ℤ))
    (localizedNewton_spec : ∀ p : ℕ, 0 < p →
      BivariantClass.IsLocalizedExtension δ X i₁ i₂ (p : ℤ)
        (ChernClass.Derived.newtonClass δ (i₂ ≫ X.hom)
          (classes.reanchor (Over.mk (i₂ ≫ X.hom))) E₂ perfect defined p)
        (localizedNewton p))
    (localizedChern_spec : ∀ p : ℕ, 0 < p →
      BivariantClass.IsLocalizedExtension δ X i₁ i₂ (p : ℤ)
        (ChernClass.Derived.totalClass δ (i₂ ≫ X.hom)
          (classes.reanchor (Over.mk (i₂ ≫ X.hom))) E₂ perfect defined p)
        (localizedChern p)),
    localizedNewton 2 =
      BivariantClass.pointwiseAdd δ
        (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 2
        (BivariantClass.Cutoff.relativeMul δ
          (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 1 1
          (localizedChern 1)
          (localizedChern 1))
        (BivariantClass.pointwiseNeg δ
          (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 2
          (BivariantClass.pointwiseNsmul δ
            (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 2
            (localizedChern 2)
            2)))

/- Lemma 42.47.7 (3): The third localized Newton class of a perfect complex vanishing on the intersection
of a two-member closed cover is `c₁³ - 3c₁c₂ + 3c₃`, with relative multiplication. -/
@[stacks 0FAK]
#check (AlgebraicGeometry.LocalizedChern.localizedNewtonClass_three :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S]
    {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom]
    {X₁ X₂ : Scheme.{u}}
    (i₁ : X₁ ⟶ X.left) (i₂ : X₂ ⟶ X.left)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (cover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (E₂ : RingedSpace.ModuleDerived X₂.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E₂)
    (defined : ChernClass.Derived.IsDefined E₂)
    (restrictionZero : IsZero
      ((RingedSpace.modulePullbackDerived (pullback.snd i₁ i₂).toShHom).obj E₂))
    (classes : ChernClass.Theory δ X.hom)
    (localizedNewton localizedChern :
      (p : ℕ) → BivariantClass δ
        (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) (p : ℤ))
    (localizedNewton_spec : ∀ p : ℕ, 0 < p →
      BivariantClass.IsLocalizedExtension δ X i₁ i₂ (p : ℤ)
        (ChernClass.Derived.newtonClass δ (i₂ ≫ X.hom)
          (classes.reanchor (Over.mk (i₂ ≫ X.hom))) E₂ perfect defined p)
        (localizedNewton p))
    (localizedChern_spec : ∀ p : ℕ, 0 < p →
      BivariantClass.IsLocalizedExtension δ X i₁ i₂ (p : ℤ)
        (ChernClass.Derived.totalClass δ (i₂ ≫ X.hom)
          (classes.reanchor (Over.mk (i₂ ≫ X.hom))) E₂ perfect defined p)
        (localizedChern p)),
    localizedNewton 3 =
      BivariantClass.pointwiseAdd δ
        (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 3
        (BivariantClass.pointwiseAdd δ
          (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 3
          (BivariantClass.Cutoff.relativeMul δ
            (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 2 1
            (BivariantClass.Cutoff.relativeMul δ
              (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 1 1
              (localizedChern 1)
              (localizedChern 1))
            (localizedChern 1))
          (BivariantClass.pointwiseNeg δ
            (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 3
            (BivariantClass.pointwiseNsmul δ
              (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 3
              (BivariantClass.Cutoff.relativeMul δ
                (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 1 2
                (localizedChern 1)
                (localizedChern 2))
              3)))
        (BivariantClass.pointwiseNsmul δ
          (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 3
          (localizedChern 3)
          3))

/- Lemma 42.47.7 (4): The fourth localized Newton class of a perfect complex vanishing on the intersection
of a two-member closed cover is `c₁⁴ - 4c₁²c₂ + 4c₁c₃ + 2c₂² - 4c₄`,
with relative multiplication. -/
@[stacks 0FAK]
#check (AlgebraicGeometry.LocalizedChern.localizedNewtonClass_four :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S]
    {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom]
    {X₁ X₂ : Scheme.{u}}
    (i₁ : X₁ ⟶ X.left) (i₂ : X₂ ⟶ X.left)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (cover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (E₂ : RingedSpace.ModuleDerived X₂.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E₂)
    (defined : ChernClass.Derived.IsDefined E₂)
    (restrictionZero : IsZero
      ((RingedSpace.modulePullbackDerived (pullback.snd i₁ i₂).toShHom).obj E₂))
    (classes : ChernClass.Theory δ X.hom)
    (localizedNewton localizedChern :
      (p : ℕ) → BivariantClass δ
        (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) (p : ℤ))
    (localizedNewton_spec : ∀ p : ℕ, 0 < p →
      BivariantClass.IsLocalizedExtension δ X i₁ i₂ (p : ℤ)
        (ChernClass.Derived.newtonClass δ (i₂ ≫ X.hom)
          (classes.reanchor (Over.mk (i₂ ≫ X.hom))) E₂ perfect defined p)
        (localizedNewton p))
    (localizedChern_spec : ∀ p : ℕ, 0 < p →
      BivariantClass.IsLocalizedExtension δ X i₁ i₂ (p : ℤ)
        (ChernClass.Derived.totalClass δ (i₂ ≫ X.hom)
          (classes.reanchor (Over.mk (i₂ ≫ X.hom))) E₂ perfect defined p)
        (localizedChern p)),
    localizedNewton 4 =
      BivariantClass.pointwiseAdd δ
        (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 4
        (BivariantClass.pointwiseAdd δ
          (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 4
          (BivariantClass.pointwiseAdd δ
            (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 4
            (BivariantClass.pointwiseAdd δ
              (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 4
              (BivariantClass.Cutoff.relativeMul δ
                (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 3 1
                (BivariantClass.Cutoff.relativeMul δ
                  (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 2 1
                  (BivariantClass.Cutoff.relativeMul δ
                    (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 1 1
                    (localizedChern 1)
                    (localizedChern 1))
                  (localizedChern 1))
                (localizedChern 1))
              (BivariantClass.pointwiseNeg δ
                (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 4
                (BivariantClass.pointwiseNsmul δ
                  (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 4
                  (BivariantClass.Cutoff.relativeMul δ
                    (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 2 2
                    (BivariantClass.Cutoff.relativeMul δ
                      (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 1 1
                      (localizedChern 1)
                      (localizedChern 1))
                    (localizedChern 2))
                  4)))
            (BivariantClass.pointwiseNsmul δ
              (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 4
              (BivariantClass.Cutoff.relativeMul δ
                (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 1 3
                (localizedChern 1)
                (localizedChern 3))
              4))
          (BivariantClass.pointwiseNsmul δ
            (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 4
            (BivariantClass.Cutoff.relativeMul δ
              (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 2 2
              (localizedChern 2)
              (localizedChern 2))
            2))
        (BivariantClass.pointwiseNeg δ
          (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 4
          (BivariantClass.pointwiseNsmul δ
            (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 4
            (localizedChern 4)
            4)))

/- Lemma 42.47.7 (5): The localized Newton classes of a perfect complex vanishing on the intersection
of a two-member closed cover satisfy the integral Newton recurrence in its localized
Chern classes, with relative multiplication. -/
@[stacks 0FAK]
#check (AlgebraicGeometry.LocalizedChern.localizedNewtonClass_succ :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S]
    {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom]
    {X₁ X₂ : Scheme.{u}}
    (i₁ : X₁ ⟶ X.left) (i₂ : X₂ ⟶ X.left)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (cover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
    (E₂ : RingedSpace.ModuleDerived X₂.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E₂)
    (defined : ChernClass.Derived.IsDefined E₂)
    (restrictionZero : IsZero
      ((RingedSpace.modulePullbackDerived (pullback.snd i₁ i₂).toShHom).obj E₂))
    (classes : ChernClass.Theory δ X.hom)
    (localizedNewton localizedChern :
      (p : ℕ) → BivariantClass δ
        (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) (p : ℤ))
    (localizedNewton_spec : ∀ p : ℕ, 0 < p →
      BivariantClass.IsLocalizedExtension δ X i₁ i₂ (p : ℤ)
        (ChernClass.Derived.newtonClass δ (i₂ ≫ X.hom)
          (classes.reanchor (Over.mk (i₂ ≫ X.hom))) E₂ perfect defined p)
        (localizedNewton p))
    (localizedChern_spec : ∀ p : ℕ, 0 < p →
      BivariantClass.IsLocalizedExtension δ X i₁ i₂ (p : ℤ)
        (ChernClass.Derived.totalClass δ (i₂ ≫ X.hom)
          (classes.reanchor (Over.mk (i₂ ≫ X.hom))) E₂ perfect defined p)
        (localizedChern p))
    (n : ℕ),
    localizedNewton (n + 1) =
      BivariantClass.pointwiseAdd δ
        (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) ((n + 1 : ℕ) : ℤ)
        (BivariantClass.pointwiseSum δ
          (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) ((n + 1 : ℕ) : ℤ)
          (Finset.univ : Finset (Finset.range n))
          (fun j ↦ BivariantClass.pointwiseZsmul δ
            (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) ((n + 1 : ℕ) : ℤ)
            (BivariantClass.Nonnegative.castGrading δ
              (localizedNewtonClass_succ_degree n j.1 j.2)
              (BivariantClass.Cutoff.relativeMul δ
                (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X)
                ((j.1 + 1 : ℕ) : ℤ) ((n - j.1 : ℕ) : ℤ)
                (localizedChern (j.1 + 1)) (localizedNewton (n - j.1))))
            ((-1 : ℤ) ^ j.1)))
        (BivariantClass.pointwiseZsmul δ
          (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) ((n + 1 : ℕ) : ℤ)
          (localizedChern (n + 1)) ((-1 : ℤ) ^ n * (n + 1 : ℕ))))

end AlgebraicGeometry.LocalizedChern
