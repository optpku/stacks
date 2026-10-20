/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Limits.ExactFunctor

@[expose] public section
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe vC uC vD uD

namespace ActualMappedResolution
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
variable [Abelian C] [Abelian D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable {M : C} (I : InjectiveResolution M) (J : InjectiveResolution (F.obj M))

/-- Apply the actual exact coefficient functor to the source resolution. -/
abbrev complex : CochainComplex D ℕ := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex

/-- Exactness at degree zero uses only exactness of F, not preservation of injectives. -/
theorem exactZero :
    (ShortComplex.mk (F.map (I.ι.f 0)) ((complex F I).d 0 1) sorry).Exact := sorry

/-- Exactness of the mapped resolution in positive degrees. -/
theorem exactSucc (n : ℕ) :
    (ShortComplex.mk ((complex F I).d n (n + 1)) ((complex F I).d (n + 1) (n + 2))
      ((complex F I).d_comp_d n (n + 1) (n + 2))).Exact := sorry

/-- The zeroth comparison extends the target augmentation along the mapped source augmentation. -/
instance mappedAugmentation_mono : Mono (F.map (I.ι.f 0)) := sorry

/-- The actual injective extension of the target augmentation along the mapped monomorphism. -/
def zero : (complex F I).X 0 ⟶ J.cocomplex.X 0 :=
  @Injective.factorThru _ _ _ _ _ _ (J.ι.f 0) (F.map (I.ι.f 0)) (mappedAugmentation_mono F I)

/-- The first comparison component is the exactness/injectivity descent of the zeroth differential. -/
def one : (complex F I).X 1 ⟶ J.cocomplex.X 1 :=
  (exactZero F I).descToInjective (zero F I J ≫ J.cocomplex.d 0 1) sorry

/-- The constructed first two components commute with the first differential. -/
theorem zero_one_comm : (complex F I).d 0 1 ≫ one F I J = zero F I J ≫ J.cocomplex.d 0 1 := sorry

/-- Each successive component is the actual descent supplied by exactness and target injectivity. -/
def succ (n : ℕ) (g : (complex F I).X n ⟶ J.cocomplex.X n)
    (g' : (complex F I).X (n + 1) ⟶ J.cocomplex.X (n + 1))
    (w : (complex F I).d n (n + 1) ≫ g' = g ≫ J.cocomplex.d n (n + 1)) :
    Σ' g'' : (complex F I).X (n + 2) ⟶ J.cocomplex.X (n + 2),
      (complex F I).d (n + 1) (n + 2) ≫ g'' = g' ≫ J.cocomplex.d (n + 1) (n + 2) :=
  ⟨(exactSucc F I n).descToInjective (g' ≫ J.cocomplex.d (n + 1) (n + 2)) sorry, sorry⟩

/-- The full cochain comparison is built recursively from the specified injective lifts. -/
def map : complex F I ⟶ J.cocomplex :=
  CochainComplex.mkHom _ _ (zero F I J) (one F I J) (zero_one_comm F I J).symm
    (fun n ⟨g, g', w⟩ ↦ ⟨(succ F I J n g g' w.symm).1, (succ F I J n g g' w.symm).2.symm⟩)

/-- The actual comparison extends the identity map of the coefficient object. -/
theorem map_augmentation : F.map (I.ι.f 0) ≫ (map F I J).f 0 = J.ι.f 0 := sorry

end ActualMappedResolution
