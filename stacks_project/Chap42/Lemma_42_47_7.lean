/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Definition_42_46_3_DerivedChern
public import stacks_project.Chap42.Lemma_42_35_4_Additive
public import stacks_project.Chap42.Lemma_42_47_1_LocalizedClass
public import stacks_project.Chap42.Lemma_42_47_11_IntersectionProduct
public import stacks_project.Chap42.Remark_42_34_7_Cutoff

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/-- Complementary relative degrees in the Newton recurrence add to the successor degree. -/
theorem localizedNewtonClass_succ_degree (n j : ℕ) (hj : j ∈ Finset.range n) :
    ((j + 1 : ℕ) : ℤ) + ((n - j : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) := sorry

section

variable {S : Scheme.{u}} [UniversallyCatenary S]
variable {δ : S → ℤ} [IsDimensionFunction δ]
variable {X : Over S} [LocallyOfFiniteType X.hom]
variable {X₁ X₂ : Scheme.{u}}
variable (i₁ : X₁ ⟶ X.left) (i₂ : X₂ ⟶ X.left)
variable [IsClosedImmersion i₁] [IsClosedImmersion i₂]
variable (cover : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)
variable (E₂ : RingedSpace.ModuleDerived X₂.toRingedSpace)
variable (perfect : RingedSpace.ModuleDerived.IsPerfect E₂)
variable (defined : ChernClass.Derived.IsDefined E₂)
variable (restrictionZero : IsZero
  ((RingedSpace.modulePullbackDerived (pullback.snd i₁ i₂).toShHom).obj E₂))
variable (classes : ChernClass.Theory δ X.hom)
variable (localizedNewton localizedChern :
  (p : ℕ) → BivariantClass δ
    (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) (p : ℤ))
variable (localizedNewton_spec : ∀ p : ℕ, 0 < p →
  BivariantClass.IsLocalizedExtension δ X i₁ i₂ (p : ℤ)
    (ChernClass.Derived.newtonClass δ (i₂ ≫ X.hom)
      (classes.reanchor (Over.mk (i₂ ≫ X.hom))) E₂ perfect defined p)
    (localizedNewton p))
variable (localizedChern_spec : ∀ p : ℕ, 0 < p →
  BivariantClass.IsLocalizedExtension δ X i₁ i₂ (p : ℤ)
    (ChernClass.Derived.totalClass δ (i₂ ≫ X.hom)
      (classes.reanchor (Over.mk (i₂ ≫ X.hom))) E₂ perfect defined p)
    (localizedChern p))

include cover restrictionZero localizedNewton_spec localizedChern_spec

/-- Lemma 42.47.7 (1): in the closed-cover setup of Lemma 42.47.1, if `E₂` restricts to
zero on `X₁ ∩ X₂`, then the localized Newton class `P' 1 (E₂)` equals the localized
Chern class `c' 1 (E₂)`. -/
@[stacks 0FAK]
theorem localizedNewtonClass_one :
    localizedNewton 1 = localizedChern 1 := sorry

/-- Lemma 42.47.7 (2): in the same restriction-zero setup, `P' 2 (E₂)` equals
`c' 1 (E₂) * c' 1 (E₂) - 2 • c' 2 (E₂)`, with relative multiplication as in
Remark 42.34.7. -/
@[stacks 0FAK]
theorem localizedNewtonClass_two :
    localizedNewton 2 =
      BivariantClass.Cutoff.relativeMul δ
          (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 1 1
          (localizedChern 1) (localizedChern 1) -
        2 • localizedChern 2 := sorry

/-- Lemma 42.47.7 (3): in the same restriction-zero setup,
`P' 3 (E₂) = c' 1 (E₂)^3 - 3 • (c' 1 (E₂) * c' 2 (E₂)) + 3 • c' 3 (E₂)`,
with relative multiplication as in Remark 42.34.7. -/
@[stacks 0FAK]
theorem localizedNewtonClass_three :
    localizedNewton 3 =
      BivariantClass.Cutoff.relativeMul δ
          (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 2 1
          (BivariantClass.Cutoff.relativeMul δ
            (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 1 1
            (localizedChern 1) (localizedChern 1))
          (localizedChern 1) -
        3 • BivariantClass.Cutoff.relativeMul δ
          (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 1 2
          (localizedChern 1) (localizedChern 2) +
        3 • localizedChern 3 := sorry

/-- Lemma 42.47.7 (4): in the same restriction-zero setup, `P' 4 (E₂)` is the usual
fourth Newton polynomial in the localized Chern classes `c' i (E₂)`, with relative
multiplication as in Remark 42.34.7. -/
@[stacks 0FAK]
theorem localizedNewtonClass_four :
    localizedNewton 4 =
      BivariantClass.Cutoff.relativeMul δ
          (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 3 1
          (BivariantClass.Cutoff.relativeMul δ
            (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 2 1
            (BivariantClass.Cutoff.relativeMul δ
              (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 1 1
              (localizedChern 1) (localizedChern 1))
            (localizedChern 1))
          (localizedChern 1) -
        4 • BivariantClass.Cutoff.relativeMul δ
          (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 2 2
          (BivariantClass.Cutoff.relativeMul δ
            (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 1 1
            (localizedChern 1) (localizedChern 1))
          (localizedChern 2) +
        4 • BivariantClass.Cutoff.relativeMul δ
          (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 1 3
          (localizedChern 1) (localizedChern 3) +
        2 • BivariantClass.Cutoff.relativeMul δ
          (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X) 2 2
          (localizedChern 2) (localizedChern 2) -
        4 • localizedChern 4 := sorry

/-- Lemma 42.47.7 (5): in the same restriction-zero setup, the localized Newton classes
satisfy the usual integral recurrence in the localized Chern classes, with relative
multiplication as in Remark 42.34.7. -/
@[stacks 0FAK]
theorem localizedNewtonClass_succ (n : ℕ) :
    localizedNewton (n + 1) =
      (∑ j : Finset.range n,
        ((-1 : ℤ) ^ j.1) •
          BivariantClass.Nonnegative.castGrading δ
            (localizedNewtonClass_succ_degree n j.1 j.2)
            (BivariantClass.Cutoff.relativeMul δ
              (Over.homMk i₂ rfl : Over.mk (i₂ ≫ X.hom) ⟶ X)
              ((j.1 + 1 : ℕ) : ℤ) ((n - j.1 : ℕ) : ℤ)
              (localizedChern (j.1 + 1)) (localizedNewton (n - j.1)))) +
        (((-1 : ℤ) ^ n * (n + 1 : ℕ)) • localizedChern (n + 1)) := sorry

end

end AlgebraicGeometry.LocalizedChern
