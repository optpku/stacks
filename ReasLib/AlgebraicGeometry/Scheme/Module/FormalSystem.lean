/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRingCat.InverseSystem
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Proper flat formal systems of scheme modules

This file bundles a sequential inverse system of rings, compatible cartesian scheme stages,
and a system of finitely presented flat module sheaves with proper support.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A proper flat formal system consists of a sequential inverse system of rings with a chosen
limit, compatible cartesian closed scheme stages, and compatible finitely presented flat module
sheaves with proper support. -/
structure ProperFlatFormalSystem where
  /-- The sequential inverse system of commutative rings. -/
  ringSystem : SequentialInverseSystem CommRingCat.{u}
  /-- The chosen limiting cone of the ring system. -/
  limitCone : LimitCone ringSystem
  /-- Every successor map in the ring system is surjective. -/
  ringMapsSurjective : ringSystem.Surjective
  /-- Every successor map in the ring system has locally nilpotent kernel. -/
  kernelsLocallyNilpotent : ringSystem.KernelLocallyNilpotent
  /-- The scheme over the limit of the ring system. -/
  scheme : Scheme.{u}
  /-- The structure morphism from the scheme to the spectrum of the limit ring. -/
  structureMap : scheme ⟶ Spec limitCone.cone.pt
  /-- The structure morphism is separated. -/
  structureMap_isSeparated : IsSeparated structureMap
  /-- The structure morphism is of finite presentation. -/
  structureMap_finitePresentation : Scheme.Hom.FinitePresentation structureMap
  /-- The scheme at each finite stage of the ring system. -/
  stageScheme : ℕ → Scheme.{u}
  /-- The map from each finite-stage scheme to the limit scheme. -/
  stageToScheme : ∀ n, stageScheme n ⟶ scheme
  /-- The structure map from each finite-stage scheme to its base ring spectrum. -/
  stageToSpec : ∀ n, stageScheme n ⟶ Spec (ringSystem.obj (Opposite.op n))
  /-- Each finite-stage scheme is the pullback of the limit scheme to its stage ring. -/
  stage_isPullback : ∀ n,
    IsPullback (stageToSpec n) (stageToScheme n)
      (Spec.map (limitCone.cone.stageMap n)) structureMap
  /-- Each finite-stage scheme maps to the limit scheme by a closed immersion. -/
  stage_isClosedImmersion : ∀ n, IsClosedImmersion (stageToScheme n)
  /-- The transition from stage `n` to stage `n + 1`. -/
  stageMap : ∀ n, stageScheme n ⟶ stageScheme (n + 1)
  /-- The stage transitions commute with the maps to the limit scheme. -/
  stageMap_comp_stageToScheme : ∀ n,
    stageMap n ≫ stageToScheme (n + 1) = stageToScheme n
  /-- The stage transitions commute with the ring-system transitions on spectra. -/
  stageMap_comp_stageToSpec : ∀ n,
    stageMap n ≫ stageToSpec (n + 1) =
      stageToSpec n ≫ Spec.map (ringSystem.stepMap n)
  /-- The module sheaf at each finite-stage scheme. -/
  moduleSheaf : ∀ n, (stageScheme n).Modules
  /-- Every finite-stage module sheaf is finitely presented. -/
  moduleSheaf_finitePresentation : ∀ n, (moduleSheaf n).IsFinitePresentation
  /-- Every finite-stage module sheaf is flat over its stage ring spectrum. -/
  moduleSheaf_flatOver : ∀ n, flatOver (moduleSheaf n) (stageToSpec n)
  /-- Every finite-stage module sheaf has proper support over its stage ring spectrum. -/
  moduleSheaf_hasProperSupport : ∀ n,
    HasProperSupportOver (stageToSpec n) (moduleSheaf n)
  /-- Pullback along a stage transition identifies the next module sheaf with the current one. -/
  moduleTransitionIso : ∀ n,
    (pullback (stageMap n)).obj (moduleSheaf (n + 1)) ≅ moduleSheaf n

namespace ProperFlatFormalSystem

/-- Bundle a proper flat formal system from its ring, scheme-stage, module, and transition data. -/
def of
    (A : SequentialInverseSystem CommRingCat.{u}) (A_lim : LimitCone A)
    (h_surjective : A.Surjective) (h_kernel : A.KernelLocallyNilpotent)
    (X : Scheme.{u}) (f : X ⟶ Spec A_lim.cone.pt)
    [IsSeparated f] [Scheme.Hom.FinitePresentation f]
    (Xn : ℕ → Scheme.{u}) (p : ∀ n, Xn n ⟶ X)
    (q : ∀ n, Xn n ⟶ Spec (A.obj (Opposite.op n)))
    (h_pullback : ∀ n,
      IsPullback (q n) (p n) (Spec.map (A_lim.cone.stageMap n)) f)
    [∀ n, IsClosedImmersion (p n)]
    (i : ∀ n, Xn n ⟶ Xn (n + 1))
    (hiX : ∀ n, i n ≫ p (n + 1) = p n)
    (hiA : ∀ n, i n ≫ q (n + 1) = q n ≫ Spec.map (A.stepMap n))
    (ℱ : ∀ n, (Xn n).Modules) [∀ n, (ℱ n).IsFinitePresentation]
    (h_flat : ∀ n, flatOver (ℱ n) (q n))
    [∀ n, HasProperSupportOver (q n) (ℱ n)]
    (φ : ∀ n, (pullback (i n)).obj (ℱ (n + 1)) ⟶ ℱ n)
    [∀ n, IsIso (φ n)] : ProperFlatFormalSystem where
  ringSystem := A
  limitCone := A_lim
  ringMapsSurjective := h_surjective
  kernelsLocallyNilpotent := h_kernel
  scheme := X
  structureMap := f
  structureMap_isSeparated := inferInstance
  structureMap_finitePresentation := inferInstance
  stageScheme := Xn
  stageToScheme := p
  stageToSpec := q
  stage_isPullback := h_pullback
  stage_isClosedImmersion := fun n ↦ inferInstance
  stageMap := i
  stageMap_comp_stageToScheme := hiX
  stageMap_comp_stageToSpec := hiA
  moduleSheaf := ℱ
  moduleSheaf_finitePresentation := fun n ↦ inferInstance
  moduleSheaf_flatOver := h_flat
  moduleSheaf_hasProperSupport := fun n ↦ inferInstance
  moduleTransitionIso := fun n ↦ asIso (φ n)

/-- `ProperFlatFormalSystem.of` preserves the supplied ring, scheme-stage, and module data, and
the forward maps of its transition isomorphisms are the supplied morphisms. -/
theorem of_spec
    (A : SequentialInverseSystem CommRingCat.{u}) (A_lim : LimitCone A)
    (h_surjective : A.Surjective) (h_kernel : A.KernelLocallyNilpotent)
    (X : Scheme.{u}) (f : X ⟶ Spec A_lim.cone.pt)
    [IsSeparated f] [Scheme.Hom.FinitePresentation f]
    (Xn : ℕ → Scheme.{u}) (p : ∀ n, Xn n ⟶ X)
    (q : ∀ n, Xn n ⟶ Spec (A.obj (Opposite.op n)))
    (h_pullback : ∀ n,
      IsPullback (q n) (p n) (Spec.map (A_lim.cone.stageMap n)) f)
    [∀ n, IsClosedImmersion (p n)]
    (i : ∀ n, Xn n ⟶ Xn (n + 1))
    (hiX : ∀ n, i n ≫ p (n + 1) = p n)
    (hiA : ∀ n, i n ≫ q (n + 1) = q n ≫ Spec.map (A.stepMap n))
    (ℱ : ∀ n, (Xn n).Modules) [∀ n, (ℱ n).IsFinitePresentation]
    (h_flat : ∀ n, flatOver (ℱ n) (q n))
    [∀ n, HasProperSupportOver (q n) (ℱ n)]
    (φ : ∀ n, (pullback (i n)).obj (ℱ (n + 1)) ⟶ ℱ n)
    [∀ n, IsIso (φ n)] :
    let S := of A A_lim h_surjective h_kernel X f Xn p q h_pullback i hiX hiA ℱ h_flat φ
    S.ringSystem = A ∧
      S.limitCone = A_lim ∧
      S.scheme = X ∧
      S.structureMap = f ∧
      S.stageScheme = Xn ∧
      S.stageToScheme = p ∧
      S.stageToSpec = q ∧
      S.stageMap = i ∧
      S.moduleSheaf = ℱ ∧
      ∀ n, (S.moduleTransitionIso n).hom = φ n := sorry

end ProperFlatFormalSystem

end AlgebraicGeometry.Scheme.Modules
