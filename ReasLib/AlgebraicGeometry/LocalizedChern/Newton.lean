module

public import ReasLib.AlgebraicGeometry.LocalizedChern.Classes
public import ReasLib.AlgebraicGeometry.BivariantClass.Cutoff.Basic
public import ReasLib.AlgebraicGeometry.BivariantClass.FiniteSum
public import ReasLib.AlgebraicGeometry.BivariantClass.Intersection

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.LocalizedChern

variable {S : Scheme.{u}} [UniversallyCatenary S]
variable {δ : S → ℤ} [IsDimensionFunction δ]
variable {X : Over S} [LocallyOfFiniteType X.hom]
variable {Z : Scheme.{u}}
variable (i : Z ⟶ X.left) [IsClosedImmersion i]
variable (classes : ChernClass.Theory δ X.hom)
variable (E : RingedSpace.ModuleDerived X.left.toRingedSpace)
variable (perfect : RingedSpace.ModuleDerived.IsPerfect E)
variable (vanishing : IsZero (restrictAway i E))
variable (finiteness : TechnicalCondition X E)

/-- The localized Newton classes of a perfect derived module vanishing off a closed center
satisfy the integral Newton recurrence in the localized Chern classes, with relative products. -/
theorem newtonClass_succ (n : ℕ) :
    newtonClass i classes E perfect vanishing finiteness (n + 1) =
      BivariantClass.pointwiseAdd δ
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) ((n + 1 : ℕ) : ℤ)
        (BivariantClass.pointwiseSum δ
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) ((n + 1 : ℕ) : ℤ)
          (Finset.range n).attach (fun j ↦
            BivariantClass.pointwiseZsmul δ
            (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) ((n + 1 : ℕ) : ℤ)
            (BivariantClass.Nonnegative.castGrading δ
              ((by
                  have hj : j.1 < n := Finset.mem_range.mp j.2
                  omega) :
                ((j.1 + 1 : ℕ) : ℤ) + ((n - j.1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ))
              (BivariantClass.Cutoff.relativeMul δ
                (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) ((j.1 + 1 : ℕ) : ℤ) ((n - j.1 : ℕ) : ℤ)
                (chernClass i classes E perfect (j.1 + 1)
                  (Scheme.ModuleDerived.rankBound_of_isZero vanishing (Nat.succ_pos j.1)) finiteness)
                (newtonClass i classes E perfect vanishing finiteness (n - j.1)))) ((-1 : ℤ) ^ j.1)))
        (BivariantClass.pointwiseZsmul δ
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) ((n + 1 : ℕ) : ℤ)
          (chernClass i classes E perfect (n + 1)
            (Scheme.ModuleDerived.rankBound_of_isZero vanishing (Nat.succ_pos n)) finiteness) ((-1 : ℤ) ^ n * (n + 1 : ℕ))) := sorry

/-- The first localized Newton class of a perfect derived module vanishing off a closed
center equals its first localized Chern class. -/
theorem newtonClass_one :
    newtonClass i classes E perfect vanishing finiteness 1 =
      chernClass i classes E perfect 1
        (Scheme.ModuleDerived.rankBound_of_isZero vanishing (Nat.succ_pos 0)) finiteness := sorry

/-- The second localized Newton class equals the relative square of the first localized
Chern class minus twice the second localized Chern class. -/
theorem newtonClass_two :
    newtonClass i classes E perfect vanishing finiteness 2 =
      BivariantClass.pointwiseAdd δ
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) 2
        (BivariantClass.Cutoff.relativeMul δ
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) 1 1
          (chernClass i classes E perfect 1
            (Scheme.ModuleDerived.rankBound_of_isZero vanishing (Nat.succ_pos 0)) finiteness)
          (chernClass i classes E perfect 1
            (Scheme.ModuleDerived.rankBound_of_isZero vanishing (Nat.succ_pos 0)) finiteness))
        (BivariantClass.pointwiseNeg δ
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) 2
          (BivariantClass.pointwiseNsmul δ
            (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) 2
            (chernClass i classes E perfect 2
              (Scheme.ModuleDerived.rankBound_of_isZero vanishing (Nat.succ_pos 1)) finiteness) 2)) := sorry

/-- The third localized Newton class equals the relative cube of the first localized
Chern class minus three times the relative product of the first and second localized Chern
classes plus three times the third localized Chern class. -/
theorem newtonClass_three :
    newtonClass i classes E perfect vanishing finiteness 3 =
      BivariantClass.pointwiseAdd δ
        (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) 3
        (BivariantClass.pointwiseAdd δ
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) 3
          (BivariantClass.Cutoff.relativeMul δ
            (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) 2 1
            (BivariantClass.Cutoff.relativeMul δ
              (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) 1 1
              (chernClass i classes E perfect 1
                (Scheme.ModuleDerived.rankBound_of_isZero vanishing (Nat.succ_pos 0)) finiteness)
              (chernClass i classes E perfect 1
                (Scheme.ModuleDerived.rankBound_of_isZero vanishing (Nat.succ_pos 0)) finiteness))
            (chernClass i classes E perfect 1
              (Scheme.ModuleDerived.rankBound_of_isZero vanishing (Nat.succ_pos 0)) finiteness))
          (BivariantClass.pointwiseNeg δ
            (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) 3
            (BivariantClass.pointwiseNsmul δ
              (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) 3
              (BivariantClass.Cutoff.relativeMul δ
                (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) 1 2
                (chernClass i classes E perfect 1
                  (Scheme.ModuleDerived.rankBound_of_isZero vanishing (Nat.succ_pos 0)) finiteness)
                (chernClass i classes E perfect 2
                  (Scheme.ModuleDerived.rankBound_of_isZero vanishing (Nat.succ_pos 1)) finiteness)) 3)))
        (BivariantClass.pointwiseNsmul δ
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) 3
          (chernClass i classes E perfect 3
            (Scheme.ModuleDerived.rankBound_of_isZero vanishing (Nat.succ_pos 2)) finiteness) 3) := sorry

end AlgebraicGeometry.LocalizedChern
