/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import ReasLib.CategoryTheory.Abelian.Projective.Dimension.Monotone
public import ReasLib.CategoryTheory.Abelian.Projective.Dimension.ShortExact
import Mathlib.Tactic.CrossRefAttribute

/-!
# Syzygies of projective presentations in `ModuleCat`

@stack 00O5

The canonical projective-dimension API lives in an arbitrary abelian category.  This leaf owns
the `ModuleCat` and raw `LinearMap` forms obtained by presenting a module as the target of a
surjection from a projective module.  It deliberately does not choose a projective resolution:
the concrete kernel of the supplied map is the public syzygy representative.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.ModuleCat

variable {R : Type u} [Ring R]

/-- The kernel of a surjective map from a projective bundled module has projective dimension one
less than its target. -/
@[stacks 00O5 "projective-presentation syzygy shift"]
theorem ker_hasProjectiveDimensionLE_of_surjective
    {F M : ModuleCat.{v} R} (pi : F ⟶ M) (hpi : Function.Surjective pi.hom)
    [Projective F] {n : ℕ} (hM : HasProjectiveDimensionLE M (n + 1)) :
    HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker pi.hom)) n := sorry

/-- The kernel of a projective presentation of an object of projective dimension at most one is
projective. -/
@[stacks 00O5 "projective kernel of a projective presentation"]
theorem ker_projective_of_surjective
    {F M : ModuleCat.{v} R} (pi : F ⟶ M) (hpi : Function.Surjective pi.hom)
    [Projective F] (hM : HasProjectiveDimensionLE M 1) :
    Projective (ModuleCat.of R (LinearMap.ker pi.hom)) := sorry

/-- In an exact finite chain of projective bundled modules, the kernel of the top differential is
projective under any projective-dimension bound no larger than the number of projective terms.

The explicit bound parameter makes the sharp `e + 1` source formulation and the usual `e + 2`
syzygy formulation share one owner, rather than weakening the former by an unnecessary successor
step. -/
@[stacks 00O5 "top syzygy projectivity from a dimension bound"]
theorem topKernel_projective_of_exact_of_dimLE
    {e : ℕ} {M : ModuleCat.{v} R} {F : Fin (e + 2) → ModuleCat.{v} R}
    (hF : ∀ i, Projective (F i))
    (d : (i : Fin (e + 1)) → F i.succ ⟶ F i.castSucc) (pi : F 0 ⟶ M)
    (hpi : Function.Surjective pi.hom)
    (hExactZero : Function.Exact (d 0).hom pi.hom)
    (hExact : ∀ i : Fin e, Function.Exact (d i.succ).hom (d i.castSucc).hom)
    {n : ℕ} (hM : HasProjectiveDimensionLE M n) (hn : n ≤ e + 2) :
    Projective (ModuleCat.of R (LinearMap.ker (d (Fin.last e)).hom)) := sorry

/-- The top syzygy criterion at its natural `e + 2` bound. -/
@[stacks 00O5 "projectivity of the top syzygy"]
theorem topKernel_projective_of_exact
    {e : ℕ} {M : ModuleCat.{v} R} {F : Fin (e + 2) → ModuleCat.{v} R}
    (hF : ∀ i, Projective (F i))
    (d : (i : Fin (e + 1)) → F i.succ ⟶ F i.castSucc) (pi : F 0 ⟶ M)
    (hpi : Function.Surjective pi.hom)
    (hExactZero : Function.Exact (d 0).hom pi.hom)
    (hExact : ∀ i : Fin e, Function.Exact (d i.succ).hom (d i.castSucc).hom)
    (hM : HasProjectiveDimensionLE M (e + 2)) :
    Projective (ModuleCat.of R (LinearMap.ker (d (Fin.last e)).hom)) := sorry

end CategoryTheory.ModuleCat

namespace LinearMap

variable {R : Type u} [Ring R]

/-- The raw linear-map form of the projective-presentation syzygy shift. -/
@[stacks 00O5 "linear-map projective-presentation syzygy shift"]
theorem ker_hasProjectiveDimensionLE_of_surjective
    {F M : Type v} [AddCommGroup F] [Module R F] [AddCommGroup M] [Module R M]
    (pi : F →ₗ[R] M) (hpi : Function.Surjective pi) [Module.Projective R F]
    {n : ℕ} (hM : HasProjectiveDimensionLE (ModuleCat.of R M) (n + 1)) :
    HasProjectiveDimensionLE (ModuleCat.of R (ker pi)) n := sorry

/-- The raw linear-map form of projectivity of the first syzygy of a projective presentation.

The ring must be small in the modules' universe to convert categorical projectivity into
module projectivity. The bundled version has no such restriction. -/
@[stacks 00O5 "linear-map projective kernel"]
theorem ker_projective_of_surjective [Small.{v} R]
    {F M : Type v} [AddCommGroup F] [Module R F] [AddCommGroup M] [Module R M]
    (pi : F →ₗ[R] M) (hpi : Function.Surjective pi) [Module.Projective R F]
    (hM : HasProjectiveDimensionLE (ModuleCat.of R M) 1) :
    Module.Projective R (ker pi) := by
  exact (IsProjective.iff_projective (R := R) _).2
    (CategoryTheory.ModuleCat.ker_projective_of_surjective (ModuleCat.ofHom pi) hpi hM)

/-- The raw linear-map form of the top syzygy criterion with an explicit dimension bound.

Smallness of the ring permits the passage from categorical to module projectivity. -/
@[stacks 00O5 "linear-map top syzygy projectivity from a dimension bound"]
theorem topKernel_projective_of_exact_of_dimLE [Small.{v} R]
    {e : ℕ} {M : Type v} [AddCommGroup M] [Module R M]
    {F : Fin (e + 2) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]
    (hF : ∀ i, Module.Projective R (F i))
    (d : (i : Fin (e + 1)) → F i.succ →ₗ[R] F i.castSucc) (pi : F 0 →ₗ[R] M)
    (hpi : Function.Surjective pi)
    (hExactZero : Function.Exact (d 0) pi)
    (hExact : ∀ i : Fin e, Function.Exact (d i.succ) (d i.castSucc))
    {n : ℕ} (hM : HasProjectiveDimensionLE (ModuleCat.of R M) n) (hn : n ≤ e + 2) :
    Module.Projective R (ker (d (Fin.last e))) := by
  exact (IsProjective.iff_projective (R := R) _).2
    (CategoryTheory.ModuleCat.topKernel_projective_of_exact_of_dimLE
      (F := fun i => ModuleCat.of R (F i))
      (fun i => (IsProjective.iff_projective (R := R) (F i)).1 (hF i))
      (fun i => ModuleCat.ofHom (d i)) (ModuleCat.ofHom pi) hpi hExactZero hExact hM hn)

/-- The raw linear-map top syzygy criterion at its natural `e + 2` bound.

Smallness of the ring permits the passage from categorical to module projectivity. -/
@[stacks 00O5 "linear-map top syzygy projectivity"]
theorem topKernel_projective_of_exact [Small.{v} R]
    {e : ℕ} {M : Type v} [AddCommGroup M] [Module R M]
    {F : Fin (e + 2) → Type v}
    [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]
    (hF : ∀ i, Module.Projective R (F i))
    (d : (i : Fin (e + 1)) → F i.succ →ₗ[R] F i.castSucc) (pi : F 0 →ₗ[R] M)
    (hpi : Function.Surjective pi)
    (hExactZero : Function.Exact (d 0) pi)
    (hExact : ∀ i : Fin e, Function.Exact (d i.succ) (d i.castSucc))
    (hM : HasProjectiveDimensionLE (ModuleCat.of R M) (e + 2)) :
    Module.Projective R (ker (d (Fin.last e))) := by
  exact topKernel_projective_of_exact_of_dimLE hF d pi hpi hExactZero hExact hM le_rfl

end LinearMap
