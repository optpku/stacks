module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.Algebra.Category.CommRingCat.InverseSystem
public import ReasLib.RingTheory.Ideal.Quotient.Pow
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ideal-Power Quotient Systems

This file owns the sequential inverse system `A ⧸ I ^ n` of quotient rings and its positive
shift `A ⧸ I ^ (n + 1)`.  Both systems have canonical cones from `A`; the positive system also
has nilpotent successor kernels.
@stack 09AU
@stack 09AV
@stack 09AW
-/

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory.CommRingCat.IdealPower

variable {A : Type u} [CommRing A]

/-- Stage `n` of the ideal-power quotient system is `A ⧸ I ^ n`. -/
abbrev stage (I : Ideal A) (n : ℕ) : CommRingCat.{u} :=
  CommRingCat.of (A ⧸ I ^ n)

/-- The successor transition from `A ⧸ I ^ (n + 1)` to `A ⧸ I ^ n`. -/
abbrev step (I : Ideal A) (n : ℕ) : stage I (n + 1) ⟶ stage I n :=
  CommRingCat.ofHom (Ideal.Quotient.factorPowSucc I n)

/-- The sequential inverse system of all ideal-power quotients of `A`. -/
@[stacks 093M "ideal-power quotient ring inverse system"]
abbrev system (I : Ideal A) : SequentialInverseSystem CommRingCat.{u} :=
  Functor.ofOpSequence (step I)

/-- The quotient homomorphism from `A` to stage `n`. -/
abbrev projection (I : Ideal A) (n : ℕ) : CommRingCat.of A ⟶ stage I n :=
  CommRingCat.ofHom (Ideal.Quotient.mk (I ^ n))

/-- The quotient projections commute with each successor transition. -/
theorem projection_naturality (I : Ideal A) (n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj (CommRingCat.of A)).map
          (homOfLE (Nat.le_add_right n 1)).op ≫ projection I n =
      projection I (n + 1) ≫
        (system I).map (homOfLE (Nat.le_add_right n 1)).op := sorry

/-- The canonical cone from `A` to its ideal-power quotient system. -/
@[stacks 093M "canonical cone to the ideal-power quotient system"]
def cone (I : Ideal A) : Limits.Cone (system I) where
  pt := CommRingCat.of A
  π := NatTrans.ofOpSequence (fun n ↦ projection I n) (projection_naturality I)

/-- The underlying homomorphism of the system transition is the quotient transition. -/
theorem stepMap_hom (I : Ideal A) (n : ℕ) :
    ((system I).stepMap n).hom = (step I n).hom := sorry

/-- The `n`th leg of the canonical cone is the quotient homomorphism. -/
theorem cone_stageMap_hom (I : Ideal A) (n : ℕ) :
    ((cone I).stageMap n).hom = (projection I n).hom := sorry

/-- Every successor transition of the ideal-power quotient system is surjective. -/
theorem step_surjective (I : Ideal A) (n : ℕ) :
    Function.Surjective ((system I).stepMap n).hom := sorry

/-- The ideal-power quotient system is a surjective inverse system. -/
theorem system_surjective (I : Ideal A) : (system I).Surjective := sorry

namespace Positive

/-- Stage `n` of the positive ideal-power system is `A ⧸ I ^ (n + 1)`. -/
abbrev stage (I : Ideal A) (n : ℕ) : CommRingCat.{u} :=
  IdealPower.stage I (n + 1)

/-- The successor transition in the positive ideal-power system. -/
abbrev step (I : Ideal A) (n : ℕ) : stage I (n + 1) ⟶ stage I n :=
  IdealPower.step I (n + 1)

/-- The sequential inverse system of positive ideal-power quotients. -/
@[stacks 09AV "ideal-power quotient ring inverse system",
  stacks 09AW "ideal-power quotient ring inverse system",
  stacks 09AU "ideal-power quotient ring inverse system"]
abbrev system (I : Ideal A) : SequentialInverseSystem CommRingCat.{u} :=
  Functor.ofOpSequence (step I)

/-- The positive ideal-power system is the first shift of the full ideal-power system. -/
theorem system_eq_shift (I : Ideal A) :
    system I = (IdealPower.system I).shift 1 := sorry

/-- The quotient homomorphism from `A` to positive stage `n`. -/
abbrev projection (I : Ideal A) (n : ℕ) : CommRingCat.of A ⟶ stage I n :=
  IdealPower.projection I (n + 1)

/-- The positive quotient projections commute with each successor transition. -/
theorem projection_naturality (I : Ideal A) (n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj (CommRingCat.of A)).map
          (homOfLE (Nat.le_add_right n 1)).op ≫ projection I n =
      projection I (n + 1) ≫
        (system I).map (homOfLE (Nat.le_add_right n 1)).op := sorry

/-- The canonical cone from `A` to its positive ideal-power quotient system. -/
@[stacks 09AV "canonical cone to the ideal-power quotient system",
  stacks 09AW "canonical cone to the ideal-power quotient system",
  stacks 09AU "canonical cone to the ideal-power quotient system"]
def cone (I : Ideal A) : Limits.Cone (system I) where
  pt := CommRingCat.of A
  π := NatTrans.ofOpSequence (fun n ↦ projection I n) (projection_naturality I)

/-- The ambient algebra maps are compatible with each positive successor transition. -/
theorem algebraMap_step (I : Ideal A) (n : ℕ) :
    algebraMap A (stage I n : Type u) =
      (step I n).hom.comp (algebraMap A (stage I (n + 1) : Type u)) := sorry

/-- The underlying homomorphism of a positive system transition is the quotient transition. -/
theorem stepMap_hom (I : Ideal A) (n : ℕ) :
    ((system I).stepMap n).hom = (step I n).hom := sorry

/-- The `n`th leg of the positive canonical cone is the quotient homomorphism. -/
theorem cone_stageMap_hom (I : Ideal A) (n : ℕ) :
    ((cone I).stageMap n).hom = (projection I n).hom := sorry

/-- Every successor transition of the positive ideal-power system is surjective. -/
theorem step_surjective (I : Ideal A) (n : ℕ) :
    Function.Surjective ((system I).stepMap n).hom := sorry

/-- Every positive successor transition has nilpotent kernel. -/
@[stacks 09AV "nilpotent ideal-power transition kernel",
  stacks 09AW "nilpotent ideal-power transition kernel",
  stacks 09AU "nilpotent ideal-power transition kernel"]
theorem step_kernel_isNilpotent (I : Ideal A) (n : ℕ) :
    IsNilpotent (RingHom.ker ((system I).stepMap n).hom) := sorry

/-- The positive ideal-power quotient system is surjective. -/
theorem system_surjective (I : Ideal A) : (system I).Surjective := sorry

/-- Positive transition kernels are nilpotent from the initial stage onward. -/
theorem system_kernelNilpotentFrom (I : Ideal A) :
    (system I).KernelNilpotentFrom 0 := sorry

/-- Any property holding at the initial positive ideal-power stage satisfies the canonical
all-stages-or-nilpotent-tail alternative. -/
@[stacks 09AV "initial property gives an ideal-power nilpotent tail",
  stacks 09AW "initial property gives an ideal-power nilpotent tail",
  stacks 09AU "initial property gives an ideal-power nilpotent tail"]
theorem allOrTail_of_zero (I : Ideal A) {P : ℕ → Prop} (h : P 0) :
    (system I).AllOrTail P := sorry

/-- Every positive transition kernel is locally nilpotent. -/
theorem system_kernelLocallyNilpotent (I : Ideal A) :
    (system I).KernelLocallyNilpotent := sorry

end Positive

end CategoryTheory.CommRingCat.IdealPower
