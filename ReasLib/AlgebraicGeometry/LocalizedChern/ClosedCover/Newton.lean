module

public import ReasLib.AlgebraicGeometry.LocalizedChern.ClosedCover
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.Newton
public import ReasLib.AlgebraicGeometry.BivariantClass.Cutoff.Basic
public import ReasLib.AlgebraicGeometry.BivariantClass.FiniteSum
public import ReasLib.AlgebraicGeometry.BivariantClass.Intersection

@[expose] public section

open CategoryTheory CategoryTheory.Limits

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

/-- The first localized Newton class of a perfect complex vanishing on the intersection
of a two-member closed cover equals its first localized Chern class. -/
theorem localizedNewtonClass_one :
    localizedNewton 1 =
      (localizedChern 1) := sorry

/-- The second localized Newton class of a perfect complex vanishing on the intersection
of a two-member closed cover is `c₁² - 2c₂`, with relative multiplication. -/
theorem localizedNewtonClass_two :
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
            2)) := sorry

/-- The third localized Newton class of a perfect complex vanishing on the intersection
of a two-member closed cover is `c₁³ - 3c₁c₂ + 3c₃`, with relative multiplication. -/
theorem localizedNewtonClass_three :
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
          3) := sorry

/-- The fourth localized Newton class of a perfect complex vanishing on the intersection
of a two-member closed cover is `c₁⁴ - 4c₁²c₂ + 4c₁c₃ + 2c₂² - 4c₄`,
with relative multiplication. -/
theorem localizedNewtonClass_four :
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
            4)) := sorry

/-- The localized Newton classes of a perfect complex vanishing on the intersection
of a two-member closed cover satisfy the integral Newton recurrence in its localized
Chern classes, with relative multiplication. -/
theorem localizedNewtonClass_succ (n : ℕ) :
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
          (localizedChern (n + 1)) ((-1 : ℤ) ^ n * (n + 1 : ℕ))) := sorry

end

end AlgebraicGeometry.LocalizedChern
