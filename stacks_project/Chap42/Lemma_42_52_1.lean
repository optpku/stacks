/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocalizedChern.Newton
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

/- Lemma 42.52.1: localized Newton classes satisfy the integral Newton identities
when the perfect derived module vanishes off the closed center. -/
@[stacks 0FBA] #check (AlgebraicGeometry.LocalizedChern.newtonClass_succ :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (vanishing : IsZero (restrictAway i E))
    (finiteness : TechnicalCondition X E) (n : ℕ),
    newtonClass i classes E perfect vanishing finiteness (n + 1) =
      BivariantClass.pointwiseAdd δ
        (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) ((n + 1 : ℕ) : ℤ)
        (BivariantClass.pointwiseSum δ
          (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) ((n + 1 : ℕ) : ℤ)
          (Finset.range n).attach (fun j ↦
            BivariantClass.pointwiseZsmul δ
            (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) ((n + 1 : ℕ) : ℤ)
            (BivariantClass.Nonnegative.castGrading δ
              ((by
                  have hj : j.1 < n := Finset.mem_range.mp j.2
                  omega) :
                ((j.1 + 1 : ℕ) : ℤ) + ((n - j.1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ))
              (BivariantClass.Cutoff.relativeMul δ
                (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) ((j.1 + 1 : ℕ) : ℤ) ((n - j.1 : ℕ) : ℤ)
                (chernClass i classes E perfect (j.1 + 1)
                  (Scheme.ModuleDerived.rankBound_of_isZero vanishing (Nat.succ_pos j.1)) finiteness)
                (newtonClass i classes E perfect vanishing finiteness (n - j.1)))) ((-1 : ℤ) ^ j.1)))
        (BivariantClass.pointwiseZsmul δ
          (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) ((n + 1 : ℕ) : ℤ)
          (chernClass i classes E perfect (n + 1)
            (Scheme.ModuleDerived.rankBound_of_isZero vanishing (Nat.succ_pos n)) finiteness) ((-1 : ℤ) ^ n * (n + 1 : ℕ))))

#check (AlgebraicGeometry.LocalizedChern.newtonClass_one :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (vanishing : IsZero (restrictAway i E))
    (finiteness : TechnicalCondition X E),
    newtonClass i classes E perfect vanishing finiteness 1 =
      chernClass i classes E perfect 1
        (Scheme.ModuleDerived.rankBound_of_isZero vanishing (Nat.succ_pos 0)) finiteness)

#check (AlgebraicGeometry.LocalizedChern.newtonClass_two :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (vanishing : IsZero (restrictAway i E))
    (finiteness : TechnicalCondition X E),
    newtonClass i classes E perfect vanishing finiteness 2 =
      BivariantClass.pointwiseAdd δ
        (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 2
        (BivariantClass.Cutoff.relativeMul δ
          (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 1 1
          (chernClass i classes E perfect 1
            (Scheme.ModuleDerived.rankBound_of_isZero vanishing (Nat.succ_pos 0)) finiteness)
          (chernClass i classes E perfect 1
            (Scheme.ModuleDerived.rankBound_of_isZero vanishing (Nat.succ_pos 0)) finiteness))
        (BivariantClass.pointwiseNeg δ
          (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 2
          (BivariantClass.pointwiseNsmul δ
            (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 2
            (chernClass i classes E perfect 2
              (Scheme.ModuleDerived.rankBound_of_isZero vanishing (Nat.succ_pos 1)) finiteness) 2)))

#check (AlgebraicGeometry.LocalizedChern.newtonClass_three :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] {δ : S → ℤ} [IsDimensionFunction δ]
    {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
    (i : Z ⟶ X.left) [IsClosedImmersion i]
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
    (perfect : RingedSpace.ModuleDerived.IsPerfect E)
    (vanishing : IsZero (restrictAway i E))
    (finiteness : TechnicalCondition X E),
    newtonClass i classes E perfect vanishing finiteness 3 =
      BivariantClass.pointwiseAdd δ
        (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 3
        (BivariantClass.pointwiseAdd δ
          (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 3
          (BivariantClass.Cutoff.relativeMul δ
            (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 2 1
            (BivariantClass.Cutoff.relativeMul δ
              (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 1 1
              (chernClass i classes E perfect 1
                (Scheme.ModuleDerived.rankBound_of_isZero vanishing (Nat.succ_pos 0)) finiteness)
              (chernClass i classes E perfect 1
                (Scheme.ModuleDerived.rankBound_of_isZero vanishing (Nat.succ_pos 0)) finiteness))
            (chernClass i classes E perfect 1
              (Scheme.ModuleDerived.rankBound_of_isZero vanishing (Nat.succ_pos 0)) finiteness))
          (BivariantClass.pointwiseNeg δ
            (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 3
            (BivariantClass.pointwiseNsmul δ
              (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 3
              (BivariantClass.Cutoff.relativeMul δ
                (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 1 2
                (chernClass i classes E perfect 1
                  (Scheme.ModuleDerived.rankBound_of_isZero vanishing (Nat.succ_pos 0)) finiteness)
                (chernClass i classes E perfect 2
                  (Scheme.ModuleDerived.rankBound_of_isZero vanishing (Nat.succ_pos 1)) finiteness)) 3)))
        (BivariantClass.pointwiseNsmul δ
          (Over.homMk i rfl : Over.mk (i ≫ X.hom) ⟶ X) 3
          (chernClass i classes E perfect 3
            (Scheme.ModuleDerived.rankBound_of_isZero vanishing (Nat.succ_pos 2)) finiteness) 3))

end AlgebraicGeometry.LocalizedChern
