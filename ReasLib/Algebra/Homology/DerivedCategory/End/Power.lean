/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Comma.Arrow
public import ReasLib.Algebra.Homology.HomologicalComplex.Double
public import ReasLib.CategoryTheory.End.Power
public import ReasLib.CategoryTheory.Pro.Sequential.Isomorphism
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived towers of endomorphism powers

The categorical power, kernel, and quotient systems are owned by `CategoryTheory.End.Power`.
This leaf adds the two-term cochain model, its derived inverse system, and the stabilized
pro-isomorphism comparison used by Lemma 20.39.2.

@stack 0H3D
@stack 091X
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v w

namespace CategoryTheory.End.Power

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The cohomological relation placing a two-term complex in degrees `-1` and `0`. -/
@[stacks 0H3D "endomorphism power two-term degree relation"]
abbrev twoTermRel : (ComplexShape.up ℤ).Rel (-1 : ℤ) 0 :=
  ComplexShape.up_mk (-1) 0 (neg_add_cancel 1)

/-- The two-term cochain complex `[M ⟶ M]` with differential `f^(n+1)`. -/
@[stacks 0H3D "endomorphism power two-term complex"]
noncomputable abbrev twoTerm {M : C} (f : End M) (n : ℕ) : CochainComplex C ℤ :=
  HomologicalComplex.double (f ^ (n + 1)) twoTermRel

section Derived

variable [HasDerivedCategory.{w} C]

/-- The functor sending an arrow to its two-term cochain complex and then to the derived
category. -/
@[stacks 0H3D "derived two-term functor on arrows"]
noncomputable abbrev twoTermFunctor : Arrow C ⥤ DerivedCategory C :=
  HomologicalComplex.double.functor C twoTermRel (neg_ne_zero.mpr one_ne_zero) ⋙
    DerivedCategory.Q

/-- The derived object represented by the endomorphism power two-term complex. -/
@[stacks 0H3D "derived endomorphism power two-term stage"]
noncomputable abbrev twoTermStage {M : C} (f : End M) (n : ℕ) :
    DerivedCategory C :=
  DerivedCategory.Q.obj (twoTerm f n)

/-- The transition between derived two-term stages. -/
@[stacks 0H3D "derived endomorphism power two-term transition"]
noncomputable abbrev twoTermStep {M : C} (f : End M) (n : ℕ) :
    twoTermStage f (n + 1) ⟶ twoTermStage f n :=
  twoTermFunctor.map (stepSquare f n)

/-- The inverse system of derived two-term stages of an endomorphism. -/
@[stacks 0H3D "derived endomorphism power two-term system"]
abbrev twoTermSystem {M : C} (f : End M) :
    SequentialInverseSystem (DerivedCategory C) :=
  arrowSystem f ⋙ twoTermFunctor

/-- The object at stage `n` of the derived two-term system. -/
@[simp, stacks 0H3D "derived endomorphism power two-term system object"]
theorem twoTermSystem_obj {M : C} (f : End M) (n : ℕ) :
    (twoTermSystem f).obj (op n) = twoTermStage f n := sorry

/-- The successor map of the derived two-term system. -/
@[simp, stacks 0H3D "derived endomorphism power two-term system transition"]
theorem twoTermSystem_stepMap {M : C} (f : End M) (n : ℕ) :
    (twoTermSystem f).stepMap n = twoTermStep f n := sorry

/-- The canonical derived-category map from a two-term power complex to its cokernel stage. -/
@[stacks 0H3D "derived endomorphism power cokernel augmentation"]
noncomputable abbrev augmentation :
    twoTermFunctor ⟶ Limits.coker C ⋙ DerivedCategory.singleFunctor C (0 : ℤ) :=
  Functor.whiskerRight
    (HomologicalComplex.double.toCokernel C twoTermRel (neg_ne_zero.mpr one_ne_zero))
    DerivedCategory.Q

/-- The derived stage of the cokernel tower. -/
@[stacks 0H3D "derived endomorphism power cokernel stage"]
noncomputable abbrev cokernelStage {M : C} (f : End M) (n : ℕ) : DerivedCategory C :=
  (DerivedCategory.singleFunctor C (0 : ℤ)).obj (quotientStage f n)

/-- The derived transition of the cokernel tower. -/
@[stacks 0H3D "derived endomorphism power cokernel transition"]
noncomputable abbrev cokernelStep {M : C} (f : End M) (n : ℕ) :
    cokernelStage f (n + 1) ⟶ cokernelStage f n :=
  (DerivedCategory.singleFunctor C (0 : ℤ)).map (quotientStep f n)

/-- The inverse system of derived cokernel stages. -/
@[stacks 0H3D "derived endomorphism power cokernel system"]
abbrev cokernelSystem {M : C} (f : End M) :
    SequentialInverseSystem (DerivedCategory C) :=
  quotientSystem f ⋙ DerivedCategory.singleFunctor C (0 : ℤ)

/-- The object at stage `n` of the derived cokernel system. -/
@[simp, stacks 0H3D "derived endomorphism power cokernel system object"]
theorem cokernelSystem_obj {M : C} (f : End M) (n : ℕ) :
    (cokernelSystem f).obj (op n) = cokernelStage f n := sorry

/-- The successor map of the derived cokernel system. -/
@[simp, stacks 0H3D "derived endomorphism power cokernel system transition"]
theorem cokernelSystem_stepMap {M : C} (f : End M) (n : ℕ) :
    (cokernelSystem f).stepMap n = cokernelStep f n := sorry

/-- The stagewise cokernel augmentation for the `(n+1)`st power. -/
@[stacks 0H3D "derived endomorphism power cokernel augmentation stage"]
noncomputable abbrev augmentationApp {M : C} (f : End M) (n : ℕ) :
    twoTermStage f n ⟶ cokernelStage f n :=
  augmentation.app (arrowStage f n)

/-- The augmentation of the two-term power system is the whiskering of the generic augmentation. -/
@[stacks 0H3D "derived endomorphism power cokernel augmentation system"]
abbrev augmentationSystem {M : C} (f : End M) :
    twoTermSystem f ⟶ cokernelSystem f :=
  Functor.whiskerLeft (arrowSystem f) augmentation

/-- The component of the system augmentation at stage `n`. -/
@[simp, stacks 0H3D "derived endomorphism power cokernel augmentation component"]
theorem augmentationSystem_app {M : C} (f : End M) (n : ℕ) :
    (augmentationSystem f).app (op n) = augmentationApp f n := sorry

/-- The canonical augmentation commutes with adjacent power transitions. -/
@[reassoc, stacks 0H3D "endomorphism power augmentation naturality"]
theorem augmentationApp_naturality {M : C} (f : End M) (n : ℕ) :
    twoTermStep f n ≫ augmentationApp f n =
      augmentationApp f (n + 1) ≫ cokernelStep f n := sorry

/-- The shift-inverse data is the fine-grained form of the stabilization comparison. -/
@[stacks 0H3D "stabilized endomorphism power pro-isomorphism"]
theorem existsShiftInverse {M : C} (f : End M)
    (h : kernelStabilizes f) :
    ∃ c : ℕ,
      ∃ reverse : SequentialInverseSystem.shift (cokernelSystem f) c ⟶ twoTermSystem f,
        Pro.SequentialHom.IsShiftInverse (augmentationSystem f) c reverse := sorry

/-- A specified stable kernel cutoff supplies the shifted inverse at that same cutoff. -/
@[stacks 0H3D "fixed-cutoff endomorphism power pro-isomorphism",
  stacks 091X "fixed-cutoff principal power pro-isomorphism"]
theorem existsShiftInverseAt {M : C} (f : End M) (c : ℕ)
    (h : kernelStableAt f c) :
    ∃ reverse : SequentialInverseSystem.shift (cokernelSystem f) c ⟶ twoTermSystem f,
      Pro.SequentialHom.IsShiftInverse (augmentationSystem f) c reverse := sorry

/-- Lemma 20.39.2 (0H3D): kernel stabilization makes the canonical cokernel augmentation a
pro-isomorphism. -/
@[stacks 0H3D "canonical stabilized endomorphism power pro-isomorphism"]
theorem augmentation_isIso {M : C} (f : End M) (h : kernelStabilizes f) :
    IsIso (Pro.SequentialHom.ofNatTrans (augmentationSystem f)).toHom := sorry

/-- The canonical cokernel augmentation is a pro-isomorphism at any specified stable cutoff. -/
@[stacks 0H3D "fixed-cutoff canonical endomorphism power pro-isomorphism",
  stacks 091X "canonical principal power pro-isomorphism"]
theorem augmentation_isIsoAt {M : C} (f : End M) (c : ℕ)
    (h : kernelStableAt f c) :
    IsIso (Pro.SequentialHom.ofNatTrans (augmentationSystem f)).toHom := sorry

end Derived

end CategoryTheory.End.Power
