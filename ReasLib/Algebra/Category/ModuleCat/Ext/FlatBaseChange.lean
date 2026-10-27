/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Exact
public import ReasLib.Algebra.Homology.DerivedCategory.Ext.Adjunction
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Flat base change for Ext of modules

This file specializes the Ext equivalence of an exact adjunction to extension
and restriction of scalars along a flat ring homomorphism.  The ring map is
explicit, so the API does not choose an `Algebra` structure between the rings.
@stack 05EG
-/

noncomputable section

open CategoryTheory Limits Abelian

universe u

namespace CategoryTheory.ModuleCat.Ext.FlatBaseChange

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Applying flat extension of scalars to both variables gives the direct
base-change map on Ext. -/
@[stacks 05EG "flat exact-functor map on Ext"]
noncomputable def map (f : R →+* S) (M N : ModuleCat.{u} R)
    (hf : f.Flat) (i : ℕ) :
    Ext M N i →+ Ext ((ModuleCat.extendScalars f).obj M)
      ((ModuleCat.extendScalars f).obj N) i :=
  (ModuleCat.ExtendScalars.exact f hf).obj.mapExtAddHom M N i

/-- The direct flat base-change map is contravariantly natural in its source module. -/
@[simp, stacks 05EG "flat Ext map naturality in the source"]
theorem map_naturality_left (f : R →+* S) {M M' : ModuleCat.{u} R}
    (g : M' ⟶ M) (N : ModuleCat.{u} R) (hf : f.Flat) {i : ℕ}
    (e : Ext M N i) :
    map f M' N hf i ((Ext.mk₀ g).comp e (zero_add i)) =
      (Ext.mk₀ ((ModuleCat.extendScalars f).map g)).comp
        (map f M N hf i e) (zero_add i) := by
  let F := ModuleCat.ExtendScalars.exact f hf
  change ((Ext.mk₀ g).comp e (zero_add i)).mapExactFunctor F.obj =
    (Ext.mk₀ (F.obj.map g)).comp (e.mapExactFunctor F.obj) (zero_add i)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]

/-- The direct flat base-change map is covariantly natural in its target module. -/
@[simp, stacks 05EG "flat Ext map naturality in the target"]
theorem map_naturality_right (f : R →+* S) (M : ModuleCat.{u} R)
    {N N' : ModuleCat.{u} R} (g : N ⟶ N') (hf : f.Flat) {i : ℕ}
    (e : Ext M N i) :
    map f M N' hf i (e.comp (Ext.mk₀ g) (add_zero i)) =
      (map f M N hf i e).comp
        (Ext.mk₀ ((ModuleCat.extendScalars f).map g)) (add_zero i) := by
  let F := ModuleCat.ExtendScalars.exact f hf
  change (e.comp (Ext.mk₀ g) (add_zero i)).mapExactFunctor F.obj =
    (e.mapExactFunctor F.obj).comp (Ext.mk₀ (F.obj.map g)) (add_zero i)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]

/-- The direct flat-base-change map sends a short exact sequence to the extension class of its
image under the exact extension-of-scalars functor. -/
@[simp, stacks 05EG "flat Ext map on extension classes"]
theorem map_extClass (f : R →+* S) (hf : f.Flat)
    {E : ShortComplex (ModuleCat.{u} R)} (hE : E.ShortExact) :
    map f E.X₃ E.X₁ hf 1 hE.extClass =
      (hE.map_of_exact (ModuleCat.ExtendScalars.exact f hf).obj).extClass := by
  exact Ext.mapExactFunctor_extClass (ModuleCat.ExtendScalars.exact f hf).obj hE

/-- Restrict an Ext class along a ring homomorphism and precompose with the
extension/restriction unit.  Flatness is not needed for this direction. -/
@[stacks 087N "flat base-change comparison on Ext"]
noncomputable def comparison (f : R →+* S) (M : ModuleCat.{u} R)
    (N : ModuleCat.{u} S) (i : ℕ) :
    Ext ((ModuleCat.extendScalars f).obj M) N i →+
      Ext M ((ModuleCat.restrictScalars f).obj N) i :=
  Adjunction.Ext.comparison (ModuleCat.extendRestrictScalarsAdj f) M N i

/-- Extend an Ext class along a flat ring homomorphism and postcompose with the
extension/restriction counit. -/
@[stacks 087N "adjoint flat base-change comparison on Ext"]
noncomputable def adjoint (f : R →+* S) (M : ModuleCat.{u} R)
    (N : ModuleCat.{u} S) (hf : f.Flat) (i : ℕ) :
    Ext M ((ModuleCat.restrictScalars f).obj N) i →+
      Ext ((ModuleCat.extendScalars f).obj M) N i :=
  ((Ext.mk₀ ((ModuleCat.extendRestrictScalarsAdj f).counit.app N)).postcomp
      ((ModuleCat.extendScalars f).obj M) (add_zero i)).comp
    ((ModuleCat.ExtendScalars.exact f hf).obj.mapExtAddHom M
      ((ModuleCat.restrictScalars f).obj N) i)

/-- The adjoint flat-base-change map is covariantly natural in its target module. -/
@[simp, stacks 087N "flat Ext adjoint naturality"]
theorem adjoint_naturality_right (f : R →+* S) (M : ModuleCat.{u} R)
    {N N' : ModuleCat.{u} S} (hf : f.Flat) {i : ℕ}
    (e : Ext M ((ModuleCat.restrictScalars f).obj N) i) (g : N ⟶ N') :
    adjoint f M N' hf i
        (e.comp (Ext.mk₀ ((ModuleCat.restrictScalars f).map g)) (add_zero i)) =
      (adjoint f M N hf i e).comp (Ext.mk₀ g) (add_zero i) := by
  let F := ModuleCat.ExtendScalars.exact f hf
  let adj := ModuleCat.extendRestrictScalarsAdj f
  change ((e.comp (Ext.mk₀ ((ModuleCat.restrictScalars f).map g))
      (add_zero i)).mapExactFunctor F.obj).comp (Ext.mk₀ (adj.counit.app N'))
      (add_zero i) =
    ((e.mapExactFunctor F.obj).comp (Ext.mk₀ (adj.counit.app N))
      (add_zero i)).comp (Ext.mk₀ g) (add_zero i)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  simp only [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
  exact congrArg (fun k ↦ (e.mapExactFunctor F.obj).comp (Ext.mk₀ k) (add_zero i))
    (adj.counit.naturality g)

/-- Postcomposing by the extension/restriction unit identifies the adjoint comparison with the
direct flat-base-change map. -/
@[simp, stacks 087N "flat Ext adjoint and unit bridge"]
theorem adjoint_postcomp_unit (f : R →+* S) (M N : ModuleCat.{u} R)
    (hf : f.Flat) {i : ℕ} (e : Ext M N i) :
    adjoint f M ((ModuleCat.extendScalars f).obj N) hf i
        (e.comp
          (Ext.mk₀ ((ModuleCat.extendRestrictScalarsAdj f).unit.app N))
          (add_zero i)) =
      map f M N hf i e := by
  let F := ModuleCat.ExtendScalars.exact f hf
  let adj := ModuleCat.extendRestrictScalarsAdj f
  change ((e.comp (Ext.mk₀ (adj.unit.app N)) (add_zero i)).mapExactFunctor
      F.obj).comp (Ext.mk₀ (adj.counit.app ((ModuleCat.extendScalars f).obj N)))
      (add_zero i) = e.mapExactFunctor F.obj
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
  have h : F.obj.map (adj.unit.app N) ≫
      adj.counit.app ((ModuleCat.extendScalars f).obj N) = 𝟙 (F.obj.obj N) :=
    adj.left_triangle_components N
  exact (congrArg (fun k ↦ (e.mapExactFunctor F.obj).comp (Ext.mk₀ k) (add_zero i))
    h).trans (Ext.comp_mk₀_id _)

/-- Postcomposing on the restricted target by a scalar endomorphism passes through the adjoint
flat-base-change map as scalar multiplication. -/
@[stacks 087N "flat Ext adjoint scalar compatibility"]
theorem adjoint_postcomp_smul_id (f : R →+* S) (M : ModuleCat.{u} R)
    (N : ModuleCat.{u} S) (hf : f.Flat) {i : ℕ}
    (e : Ext M ((ModuleCat.restrictScalars f).obj N) i) (a : S) :
    adjoint f M N hf i
        (e.comp
          (Ext.mk₀ ((ModuleCat.restrictScalars f).map (a • 𝟙 N))) (add_zero i)) =
      a • adjoint f M N hf i e := by
  rw [adjoint_naturality_right, ← Ext.smul_eq_comp_mk₀]

/-- The adjoint map is a left inverse to the comparison map. -/
@[simp, stacks 087N "flat Ext adjunction left inverse"]
theorem adjoint_comparison (f : R →+* S) (M : ModuleCat.{u} R)
    (N : ModuleCat.{u} S) (hf : f.Flat) (i : ℕ)
    (x : Ext ((ModuleCat.extendScalars f).obj M) N i) :
    adjoint f M N hf i (comparison f M N i x) = x := sorry

/-- The comparison map is a left inverse to the adjoint map. -/
@[simp, stacks 087N "flat Ext adjunction right inverse"]
theorem comparison_adjoint (f : R →+* S) (M : ModuleCat.{u} R)
    (N : ModuleCat.{u} S) (hf : f.Flat) (i : ℕ)
    (x : Ext M ((ModuleCat.restrictScalars f).obj N) i) :
    comparison f M N i (adjoint f M N hf i x) = x := sorry

/-- Flat base change gives the canonical additive equivalence
`Ext ((ModuleCat.extendScalars f).obj M) N i ≃+ Ext M ((ModuleCat.restrictScalars f).obj N) i`. -/
@[stacks 087N "flat base-change equivalence on Ext"]
noncomputable def equiv (f : R →+* S) (M : ModuleCat.{u} R)
    (N : ModuleCat.{u} S) (hf : f.Flat) (i : ℕ) :
    Ext ((ModuleCat.extendScalars f).obj M) N i ≃+
      Ext M ((ModuleCat.restrictScalars f).obj N) i where
  toFun := comparison f M N i
  invFun := adjoint f M N hf i
  left_inv := adjoint_comparison f M N hf i
  right_inv := comparison_adjoint f M N hf i
  map_add' := (comparison f M N i).map_add

/-- The forward map of the flat-base-change equivalence is `comparison`. -/
@[simp, stacks 087N "flat Ext equivalence forward map"]
theorem equiv_apply (f : R →+* S) (M : ModuleCat.{u} R)
    (N : ModuleCat.{u} S) (hf : f.Flat) (i : ℕ)
    (x : Ext ((ModuleCat.extendScalars f).obj M) N i) :
    equiv f M N hf i x = comparison f M N i x := by
  rfl

/-- The inverse map of the flat-base-change equivalence is `adjoint`. -/
@[simp, stacks 087N "flat Ext equivalence inverse map"]
theorem equiv_symm_apply (f : R →+* S) (M : ModuleCat.{u} R)
    (N : ModuleCat.{u} S) (hf : f.Flat) (i : ℕ)
    (x : Ext M ((ModuleCat.restrictScalars f).obj N) i) :
    (equiv f M N hf i).symm x = adjoint f M N hf i x := by
  rfl

end CategoryTheory.ModuleCat.Ext.FlatBaseChange
