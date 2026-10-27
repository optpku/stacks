/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.InverseSystem.Positive.IdealPower.Family
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Multiplication on a family of ideal powers

Multiplication by `a ∈ I ^ d` sends the fixed-degree tower for `n` to that for `d + n`, at the
same ambient stage.  Compatibility with the monic inclusions uniquely determines these maps, so
naturality in the ambient stage is a derived theorem rather than an extra field.
`Family.multiplication` constructs the maps using kernels, the ideal-subobject universal property,
and normal monomorphisms, available in particular for modules and sheaves of modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace CategoryTheory.PNatInverseSystem.IdealPower

variable {A : Type w} [CommRing A]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear A C]

/-- Multiplication by ideal-power representatives on a two-parameter ideal-power family. -/
@[stacks 0GYL "multiplication on an ideal-power family",
  stacks 0GYN "multiplication on an ideal-power family"]
structure Family.Multiplication
    {I : Ideal A} {F : PNatInverseSystem C} (P : Family I F) where
  /-- Multiplication by `a ∈ I ^ d` at one ambient stage. -/
  stageMap : ∀ d n m : ℕ, Ideal.AssociatedGraded.stage I A d →
    ((P.fixedTower n).obj (op m) ⟶ (P.fixedTower (d + n)).obj (op m))
  /-- After inclusion into the ambient tower, the stage map is ordinary scalar multiplication. -/
  stageMap_comp_fixedι : ∀ (d n m : ℕ) (a : Ideal.AssociatedGraded.stage I A d),
    stageMap d n m a ≫ (P.fixedι (d + n)).app (op m) =
      (P.fixedι n).app (op m) ≫ ((a : A) • 𝟙 _)

section Construction

/-- The mono evidence used by the normal-subobject universal property comes directly from the
family, including the identity inclusion in degree zero. -/
theorem Family.mono_fixedι_app_from_family
    {I : Ideal A} {F : PNatInverseSystem C} (P : Family I F) (n m : ℕ) :
    Mono ((P.fixedι n).app (op m)) := by
  cases n with
  | zero => exact inferInstanceAs (Mono (𝟙 (F.toSequential.obj (op m))))
  | succ n => exact (P.isSMulSubobject (Nat.succPNat n) m).1

/-- Scalar multiplication carries the degree-`n` ideal subobject into degree `d + n` at the
same ambient stage: it is killed by every morphism killing the target ideal subobject. -/
theorem Family.fixedι_comp_smul_comp_zero
    [HasKernels C]
    {I : Ideal A} {F : PNatInverseSystem C} (P : Family I F)
    (d n m : ℕ) (a : Ideal.AssociatedGraded.stage I A d)
    {T : C} (q : F.toSequential.obj (op m) ⟶ T)
    (hq : (P.fixedι (d + n)).app (op m) ≫ q = 0) :
    ((P.fixedι n).app (op m) ≫ ((a : A) • 𝟙 _)) ≫ q = 0 := sorry

variable [HasKernels C] [IsNormalMonoCategory C]

/-- The canonical same-stage map `I ^ n F (m + 1) ⟶ I ^ (d + n) F (m + 1)`, obtained by
restricting scalar multiplication to the target ideal subobject. -/
noncomputable def Family.multiplicationStageMap
    {I : Ideal A} {F : PNatInverseSystem C} (P : Family I F)
    (d n m : ℕ) (a : Ideal.AssociatedGraded.stage I A d) :
    (P.fixedTower n).obj (op m) ⟶ (P.fixedTower (d + n)).obj (op m) := by
  letI := P.mono_fixedι_app_from_family (d + n) m
  letI := normalMonoOfMono ((P.fixedι (d + n)).app (op m))
  exact (NormalMono.lift' ((P.fixedι (d + n)).app (op m))
    ((P.fixedι n).app (op m) ≫ ((a : A) • 𝟙 _))
    (P.fixedι_comp_smul_comp_zero d n m a _
      (NormalMono.w (f := (P.fixedι (d + n)).app (op m))))).1

/-- Inclusion of the constructed map is ordinary scalar multiplication on the ambient stage. -/
@[reassoc]
theorem Family.multiplicationStageMap_comp_fixedι
    {I : Ideal A} {F : PNatInverseSystem C} (P : Family I F)
    (d n m : ℕ) (a : Ideal.AssociatedGraded.stage I A d) :
    P.multiplicationStageMap d n m a ≫ (P.fixedι (d + n)).app (op m) =
      (P.fixedι n).app (op m) ≫ ((a : A) • 𝟙 _) := by
  letI := P.mono_fixedι_app_from_family (d + n) m
  letI := normalMonoOfMono ((P.fixedι (d + n)).app (op m))
  exact (NormalMono.lift' ((P.fixedι (d + n)).app (op m))
    ((P.fixedι n).app (op m) ≫ ((a : A) • 𝟙 _))
    (P.fixedι_comp_smul_comp_zero d n m a _
      (NormalMono.w (f := (P.fixedι (d + n)).app (op m))))).2

/-- The inclusion computation uniquely determines the same-stage multiplication map. -/
theorem Family.multiplicationStageMap_unique
    {I : Ideal A} {F : PNatInverseSystem C} (P : Family I F)
    (d n m : ℕ) (a : Ideal.AssociatedGraded.stage I A d)
    (f : (P.fixedTower n).obj (op m) ⟶ (P.fixedTower (d + n)).obj (op m))
    (hf : f ≫ (P.fixedι (d + n)).app (op m) =
      (P.fixedι n).app (op m) ≫ ((a : A) • 𝟙 _)) :
    f = P.multiplicationStageMap d n m a := by
  letI := P.mono_fixedι_app_from_family (d + n) m
  exact (cancel_mono ((P.fixedι (d + n)).app (op m))).1
    (hf.trans (P.multiplicationStageMap_comp_fixedι d n m a).symm)

/-- Canonical same-stage multiplication on an ideal-power family, including degree zero. -/
@[stacks 0GYL "canonical multiplication on an ideal-power family",
  stacks 0GYN "canonical multiplication on an ideal-power family"]
noncomputable def Family.multiplication
    {I : Ideal A} {F : PNatInverseSystem C} (P : Family I F) : P.Multiplication where
  stageMap := P.multiplicationStageMap
  stageMap_comp_fixedι := P.multiplicationStageMap_comp_fixedι

/-- The inclusion computation determines the whole family multiplication package. -/
theorem Family.Multiplication.eq_canonical
    {I : Ideal A} {F : PNatInverseSystem C} {P : Family I F}
    (μ : P.Multiplication) : μ = P.multiplication := sorry

end Construction

/-- Family multiplication maps commute with every transition in the ambient stage. -/
theorem Family.Multiplication.stageMap_naturality
    {I : Ideal A} {F : PNatInverseSystem C} {P : Family I F}
    (μ : P.Multiplication) (d n : ℕ) {m l : ℕ} (hml : m ≤ l)
    (a : Ideal.AssociatedGraded.stage I A d) :
    (P.fixedTower n).transitionMap hml ≫ μ.stageMap d n m a =
      μ.stageMap d n l a ≫ (P.fixedTower (d + n)).transitionMap hml := sorry

/-- The stagewise multiplication maps satisfy the naturality equation in the indexing
category. -/
theorem Family.Multiplication.natTrans_naturality
    {I : Ideal A} {F : PNatInverseSystem C} {P : Family I F}
    (μ : P.Multiplication) (d n : ℕ)
    (a : Ideal.AssociatedGraded.stage I A d)
    {m l : ℕᵒᵖ} (f : m ⟶ l) :
    (P.fixedTower n).map f ≫ μ.stageMap d n l.unop a =
      μ.stageMap d n m.unop a ≫ (P.fixedTower (d + n)).map f := sorry

/-- Multiplication by a fixed representative as a natural transformation between fixed-degree
towers. -/
@[stacks 0GYL "natural multiplication map between fixed ideal-power towers",
  stacks 0GYN "natural multiplication map between fixed ideal-power towers"]
def Family.Multiplication.natTrans
    {I : Ideal A} {F : PNatInverseSystem C} {P : Family I F}
    (μ : P.Multiplication) (d n : ℕ)
    (a : Ideal.AssociatedGraded.stage I A d) :
    P.fixedTower n ⟶ P.fixedTower (d + n) where
  app m := μ.stageMap d n m.unop a
  naturality _ _ f := μ.natTrans_naturality d n a f

end CategoryTheory.PNatInverseSystem.IdealPower
