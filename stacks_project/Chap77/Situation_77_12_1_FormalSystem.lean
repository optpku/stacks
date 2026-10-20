/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

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

This file bundles a sequential inverse system of rings, compatible cartesian algebraic-space
stages, and a system of finitely presented flat module sheaves with proper support.

Relative flatness is the global form of Comparison-side `flatOverAt`, so this module can be
imported together with `HasProperSupportOver`; `Lemma_67_31_3_FlatOver` independently declares
`schemeEtaleRingedHom` and cannot be imported in the same environment.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- `Spec(A_n)` as an algebraic space over `Spec A`, where `A` is the vertex of the chosen
limit cone. -/
abbrev stageSpec {A : SequentialInverseSystem CommRingCat.{u}} (A_lim : LimitCone A) (n : ℕ) :
    AlgebraicSpace (Spec A_lim.cone.pt) :=
  ofOver (Over.mk (Spec.map (A_lim.cone.stageMap n)))

/-- The canonical morphism `Spec(A_n) ⟶ Spec A` in `AlgebraicSpace (Spec A)`. -/
def stageSpecToBase {A : SequentialInverseSystem CommRingCat.{u}} (A_lim : LimitCone A) (n : ℕ) :
    stageSpec A_lim n ⟶ ofOver (Over.mk (𝟙 (Spec A_lim.cone.pt))) :=
  ofOverHomMk (Spec.map (A_lim.cone.stageMap n)) (Category.comp_id _)

/-- Compatibility of `Spec.map (A.stepMap n)` with the cone maps to `Spec A`. -/
theorem stageSpecTransition_over {A : SequentialInverseSystem CommRingCat.{u}}
    (A_lim : LimitCone A) (n : ℕ) :
    Spec.map (A.stepMap n) ≫ Spec.map (A_lim.cone.stageMap (n + 1)) =
      Spec.map (A_lim.cone.stageMap n) := sorry

/-- The morphism `Spec(A_n) ⟶ Spec(A_{n+1})` of algebraic spaces over `Spec A` induced by the
successor map of the ring system. -/
def stageSpecTransition {A : SequentialInverseSystem CommRingCat.{u}} (A_lim : LimitCone A)
    (n : ℕ) : stageSpec A_lim n ⟶ stageSpec A_lim (n + 1) :=
  ofOverHomMk (Spec.map (A.stepMap n)) (stageSpecTransition_over A_lim n)

/-- A proper flat formal system consists of a sequential inverse system of rings with a chosen
limit, compatible cartesian closed algebraic-space stages, and compatible finitely presented
flat module sheaves with proper support. -/
structure ProperFlatFormalSystem where
  /-- The sequential inverse system of commutative rings. -/
  ringSystem : SequentialInverseSystem CommRingCat.{u}
  /-- The chosen limiting cone of the ring system. -/
  limitCone : LimitCone ringSystem
  /-- Every successor map in the ring system is surjective. -/
  ringMapsSurjective : ringSystem.Surjective
  /-- Every successor map in the ring system has locally nilpotent kernel. -/
  kernelsLocallyNilpotent : ringSystem.KernelLocallyNilpotent
  /-- The algebraic space over the spectrum of the limit ring. -/
  space : AlgebraicSpace (Spec limitCone.cone.pt)
  /-- The unique morphism to the base `Spec A` is separated. -/
  toBase_separated : Separated (toBase space)
  /-- The unique morphism to the base `Spec A` is of finite presentation. -/
  toBase_finitePresentation : FinitePresentation (toBase space)
  /-- The algebraic space at each finite stage of the ring system. -/
  stageSpace : ℕ → AlgebraicSpace (Spec limitCone.cone.pt)
  /-- The map from each finite-stage algebraic space to the limit algebraic space. -/
  stageToSpace : ∀ n, stageSpace n ⟶ space
  /-- The structure map from each finite-stage algebraic space to `Spec(A_n)`. -/
  stageToSpec : ∀ n, stageSpace n ⟶ stageSpec limitCone n
  /-- Each finite-stage algebraic space is the pullback of the limit space to its stage ring. -/
  stage_isPullback : ∀ n,
    IsPullback (stageToSpec n) (stageToSpace n) (stageSpecToBase limitCone n) (toBase space)
  /-- Each finite-stage algebraic space maps to the limit space by a closed immersion. -/
  stage_isClosedImmersion : ∀ n, IsClosedImmersion (stageToSpace n)
  /-- The transition from stage `n` to stage `n + 1`. -/
  stageMap : ∀ n, stageSpace n ⟶ stageSpace (n + 1)
  /-- The stage transitions commute with the maps to the limit algebraic space. -/
  stageMap_comp_stageToSpace : ∀ n,
    stageMap n ≫ stageToSpace (n + 1) = stageToSpace n
  /-- The stage transitions commute with the ring-system transitions on spectra. -/
  stageMap_comp_stageToSpec : ∀ n,
    stageMap n ≫ stageToSpec (n + 1) = stageToSpec n ≫ stageSpecTransition limitCone n
  /-- The module sheaf at each finite-stage algebraic space. -/
  moduleSheaf : ∀ n, (stageSpace n).Modules
  /-- Every finite-stage module sheaf is finitely presented. -/
  moduleSheaf_finitePresentation : ∀ n, (moduleSheaf n).IsFinitePresentation
  /-- Every finite-stage module sheaf is flat over its stage ring spectrum. -/
  moduleSheaf_flatOver : ∀ n x, flatOverAt (moduleSheaf n) (stageToSpec n) x
  /-- Every finite-stage module sheaf has proper support over its stage ring spectrum. -/
  moduleSheaf_hasProperSupport : ∀ n, HasProperSupportOver (stageToSpec n) (moduleSheaf n)
  /-- Pullback along a stage transition identifies the next module sheaf with the current one. -/
  moduleTransitionIso : ∀ n, (pullback (stageMap n)).obj (moduleSheaf (n + 1)) ≅ moduleSheaf n

namespace ProperFlatFormalSystem

/-- Bundle a proper flat formal system from its ring, algebraic-space stage, module, and
transition data. -/
def of
    (A : SequentialInverseSystem CommRingCat.{u}) (A_lim : LimitCone A)
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
    [∀ n, IsIso (φ n)] : ProperFlatFormalSystem where
  ringSystem := A
  limitCone := A_lim
  ringMapsSurjective := h_surjective
  kernelsLocallyNilpotent := h_kernel
  space := X
  toBase_separated := inferInstance
  toBase_finitePresentation := inferInstance
  stageSpace := Xn
  stageToSpace := p
  stageToSpec := q
  stage_isPullback := h_pullback
  stage_isClosedImmersion := fun _ ↦ inferInstance
  stageMap := i
  stageMap_comp_stageToSpace := hiX
  stageMap_comp_stageToSpec := hiA
  moduleSheaf := ℱ
  moduleSheaf_finitePresentation := fun _ ↦ inferInstance
  moduleSheaf_flatOver := h_flat
  moduleSheaf_hasProperSupport := fun _ ↦ inferInstance
  moduleTransitionIso := fun n ↦ asIso (φ n)

/-- `ProperFlatFormalSystem.of` preserves the supplied ring, algebraic-space stage, and module
data, and the forward maps of its transition isomorphisms are the supplied morphisms. -/
theorem of_spec
    (A : SequentialInverseSystem CommRingCat.{u}) (A_lim : LimitCone A)
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
    [∀ n, IsIso (φ n)] :
    let S := of A A_lim h_surjective h_kernel X Xn p q h_pullback i hiX hiA ℱ h_flat φ
    S.ringSystem = A ∧
      S.limitCone = A_lim ∧
      S.space = X ∧
      S.stageSpace = Xn ∧
      S.stageToSpace = p ∧
      S.stageToSpec = q ∧
      S.stageMap = i ∧
      S.moduleSheaf = ℱ ∧
      ∀ n, (S.moduleTransitionIso n).hom = φ n := sorry

/-- The finite-stage algebraic space `X_n` viewed as a closed subspace of `X`. -/
def stageClosedSubspace (S : ProperFlatFormalSystem) (n : ℕ) : ClosedSubspace S.space where
  X := S.stageSpace n
  ι := S.stageToSpace n
  isClosedImmersion := S.stage_isClosedImmersion n

end ProperFlatFormalSystem

end AlgebraicGeometry.AlgebraicSpace.Modules

