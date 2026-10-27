/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FormalSystem
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.Algebra.Category.CommRingCat.InverseSystem
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap76.«76_42_5_1_ProperSupport»
public import stacks_project.Chap77.Theorem_77_4_7_FlatOver

/-!
# Proper flat formal systems of modules on algebraic spaces

Typed compatibility checks for the canonical formal-system constructions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

#check (stageSpec : ∀ {A : SequentialInverseSystem CommRingCat.{u}} (A_lim : LimitCone A) (n : ℕ),
    AlgebraicSpace (Spec A_lim.cone.pt))

#check (stageSpecToBase : ∀ {A : SequentialInverseSystem CommRingCat.{u}} (A_lim : LimitCone A) (n : ℕ),
    stageSpec A_lim n ⟶ ofOver (Over.mk (𝟙 (Spec A_lim.cone.pt))))

#check (stageSpecTransition_over : ∀ {A : SequentialInverseSystem CommRingCat.{u}}
    (A_lim : LimitCone A) (n : ℕ),
    Spec.map (A.stepMap n) ≫ Spec.map (A_lim.cone.stageMap (n + 1)) =
      Spec.map (A_lim.cone.stageMap n))

#check (stageSpecTransition : ∀ {A : SequentialInverseSystem CommRingCat.{u}} (A_lim : LimitCone A)
    (n : ℕ),
    stageSpec A_lim n ⟶ stageSpec A_lim (n + 1))

#check (ProperFlatFormalSystem : Type (u + 1))

#check (ProperFlatFormalSystem.of : ∀ (A : SequentialInverseSystem CommRingCat.{u}) (A_lim : LimitCone A)
    (h_surjective : A.Surjective) (h_kernel : A.KernelLocallyNilpotent)
    (X : AlgebraicSpace (Spec A_lim.cone.pt))
    [Separated (toBase X)] [FinitePresentation (toBase X)]
    (Xn : ℕ → AlgebraicSpace (Spec A_lim.cone.pt)) (p : ∀ n, Xn n ⟶ X)
    (q : ∀ n, Xn n ⟶ stageSpec A_lim n)
    (h_pullback : ∀ n, IsPullback (q n) (p n) (stageSpecToBase A_lim n) (toBase X))
    [∀ n, IsClosedImmersion (p n)]
    (i : ∀ n, Xn n ⟶ Xn (n + 1))
    (hiX : ∀ n, i n ≫ p (n + 1) = p n)
    (hiA : ∀ n, i n ≫ q (n + 1) = q n ≫ stageSpecTransition A_lim n)
    (ℱ : ∀ n, (Xn n).Modules) [∀ n, (ℱ n).IsFinitePresentation]
    (h_flat : ∀ n x, flatOverAt (ℱ n) (q n) x)
    [∀ n, HasProperSupportOver (q n) (ℱ n)]
    (φ : ∀ n, (pullback (i n)).obj (ℱ (n + 1)) ⟶ ℱ n)
    [∀ n, IsIso (φ n)],
    ProperFlatFormalSystem)

#check (ProperFlatFormalSystem.of_spec : ∀ (A : SequentialInverseSystem CommRingCat.{u}) (A_lim : LimitCone A)
    (h_surjective : A.Surjective) (h_kernel : A.KernelLocallyNilpotent)
    (X : AlgebraicSpace (Spec A_lim.cone.pt))
    [Separated (toBase X)] [FinitePresentation (toBase X)]
    (Xn : ℕ → AlgebraicSpace (Spec A_lim.cone.pt)) (p : ∀ n, Xn n ⟶ X)
    (q : ∀ n, Xn n ⟶ stageSpec A_lim n)
    (h_pullback : ∀ n, IsPullback (q n) (p n) (stageSpecToBase A_lim n) (toBase X))
    [∀ n, IsClosedImmersion (p n)]
    (i : ∀ n, Xn n ⟶ Xn (n + 1))
    (hiX : ∀ n, i n ≫ p (n + 1) = p n)
    (hiA : ∀ n, i n ≫ q (n + 1) = q n ≫ stageSpecTransition A_lim n)
    (ℱ : ∀ n, (Xn n).Modules) [∀ n, (ℱ n).IsFinitePresentation]
    (h_flat : ∀ n x, flatOverAt (ℱ n) (q n) x)
    [∀ n, HasProperSupportOver (q n) (ℱ n)]
    (φ : ∀ n, (pullback (i n)).obj (ℱ (n + 1)) ⟶ ℱ n)
    [∀ n, IsIso (φ n)],
    let S := ProperFlatFormalSystem.of A A_lim h_surjective h_kernel X Xn p q h_pullback i hiX hiA ℱ h_flat φ
    S.ringSystem = A ∧
      S.limitCone = A_lim ∧
      S.space = X ∧
      S.stageSpace = Xn ∧
      S.stageToSpace = p ∧
      S.stageToSpec = q ∧
      S.stageMap = i ∧
      S.moduleSheaf = ℱ ∧
      ∀ n, (S.moduleTransitionIso n).hom = φ n)

#check (ProperFlatFormalSystem.stageClosedSubspace : ∀ (S : ProperFlatFormalSystem) (n : ℕ),
    ClosedSubspace S.space)

end AlgebraicGeometry.AlgebraicSpace.Modules
