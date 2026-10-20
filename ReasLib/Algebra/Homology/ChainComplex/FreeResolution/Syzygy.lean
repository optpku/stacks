/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.ChainComplex.FreeResolution

/-!
# Syzygies of an augmented chain complex

@stack 00NG

This file owns the canonical syzygy tower attached to an augmentation of a chain complex to a
module concentrated in degree zero.  The tower is bundled as objects of `ModuleCat`, so its
additive and module structures are inherited from the object rather than reconstructed by local
instances at every use site.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace ChainComplex

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {F : ChainComplex (ModuleCat.{v} R) ℕ}

/-- The syzygy tower of an augmentation `π : F ⟶ moduleSingle R M`.

The zeroth object is `M`, the first object is the augmentation kernel, and the `(n + 2)`nd object
is the kernel of `F.d (n + 1) n`.  Returning a `ModuleCat` object makes the canonical module
structure available to downstream constructions without local instance pins.
-/
@[stacks 00NG "syzygy tower of an augmented resolution"]
noncomputable def syzygy (π : F ⟶ moduleSingle R M) : ℕ → ModuleCat.{v} R
  | 0 => ModuleCat.of R M
  | 1 => ModuleCat.of R (LinearMap.ker (π.f 0).hom)
  | n + 2 => ModuleCat.of R (LinearMap.ker (F.d (n + 1) n).hom)

/-- The zeroth syzygy is the augmented module itself. -/
@[simp, stacks 00NG "zeroth syzygy"]
theorem syzygy_zero (π : F ⟶ moduleSingle R M) :
    syzygy π 0 = ModuleCat.of R M := sorry

/-- The first syzygy is the kernel of the augmentation map in degree zero. -/
@[simp, stacks 00NG "first syzygy"]
theorem syzygy_one (π : F ⟶ moduleSingle R M) :
    syzygy π 1 = ModuleCat.of R (LinearMap.ker (π.f 0).hom) := sorry

/-- A positive successor syzygy is the kernel of the corresponding chain differential. -/
@[simp, stacks 00NG "successive syzygy"]
theorem syzygy_succ_succ (π : F ⟶ moduleSingle R M) (n : ℕ) :
    syzygy π (n + 2) = ModuleCat.of R (LinearMap.ker (F.d (n + 1) n).hom) := sorry

namespace Syzygy

/-- The first differential of an augmentation lands in the first syzygy. -/
@[stacks 00NG "augmentation differential lands in the syzygy kernel"]
theorem d_one_mem (π : F ⟶ moduleSingle R M) (x : F.X 1) :
    (F.d 1 0).hom x ∈ LinearMap.ker (π.f 0).hom := sorry

/-- Every positive differential lands in the preceding syzygy. -/
@[stacks 00NG "successive differential lands in the syzygy kernel"]
theorem d_succ_mem (F : ChainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) (x : F.X (n + 2)) :
    (F.d (n + 2) (n + 1)).hom x ∈ LinearMap.ker (F.d (n + 1) n).hom := sorry

/-- The canonical map from the `n`th chain term to the `n`th syzygy. -/
@[stacks 00NG "canonical map to the preceding syzygy"]
noncomputable def toPrevious (π : F ⟶ moduleSingle R M) :
    ∀ n, F.X n ⟶ syzygy π n
  | 0 => π.f 0
  | 1 => ModuleCat.ofHom <|
      LinearMap.codRestrict (LinearMap.ker (π.f 0).hom) (F.d 1 0).hom (d_one_mem π)
  | n + 2 => ModuleCat.ofHom <|
      LinearMap.codRestrict (LinearMap.ker (F.d (n + 1) n).hom)
        (F.d (n + 2) (n + 1)).hom (d_succ_mem F n)

/-- The canonical inclusion of the `(n + 1)`st syzygy into the `n`th chain term. -/
@[stacks 00NG "syzygy inclusion into the chain term"]
noncomputable def inclusion (π : F ⟶ moduleSingle R M) :
    ∀ n, syzygy π (n + 1) ⟶ F.X n
  | 0 => ModuleCat.ofHom (LinearMap.ker (π.f 0).hom).subtype
  | 1 => ModuleCat.ofHom (LinearMap.ker (F.d 1 0).hom).subtype
  | n + 2 => ModuleCat.ofHom (LinearMap.ker (F.d (n + 2) (n + 1)).hom).subtype

/-- The syzygy inclusion followed by the map to the preceding syzygy is zero. -/
@[stacks 00NG "syzygy inclusion composition"]
theorem inclusion_comp_toPrevious (π : F ⟶ moduleSingle R M) (n : ℕ) :
    inclusion π n ≫ toPrevious π n = 0 := sorry

/-- The short complex formed by two consecutive syzygy maps. -/
@[stacks 00NG "short complex of consecutive syzygies"]
noncomputable def shortComplex (π : F ⟶ moduleSingle R M) (n : ℕ) :
    ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk (inclusion π n) (toPrevious π n) (inclusion_comp_toPrevious π n)

/-- The syzygy inclusion is injective on underlying modules. -/
@[stacks 00NG "syzygy inclusion is injective"]
theorem inclusion_injective (π : F ⟶ moduleSingle R M) (n : ℕ) :
    Function.Injective (inclusion π n).hom := sorry

/-- The consecutive syzygy maps are exact at the chain term. -/
@[stacks 00NG "exactness of the syzygy row"]
theorem exact (π : F ⟶ moduleSingle R M) (n : ℕ) :
    Function.Exact (inclusion π n).hom (toPrevious π n).hom := sorry

/-- A quasi-isomorphic augmentation makes every syzygy map onto the preceding syzygy. -/
@[stacks 00NG "syzygy map is surjective for a free resolution"]
theorem toPrevious_surjective (π : F ⟶ moduleSingle R M)
    [IsFreeResolution π] (n : ℕ) :
    Function.Surjective (toPrevious π n).hom := sorry

/-- Consecutive syzygies form a short exact complex for a free resolution. -/
@[stacks 00NG "short exact syzygy row"]
theorem shortExact (π : F ⟶ moduleSingle R M) [IsFreeResolution π] (n : ℕ) :
    (shortComplex π n).ShortExact := sorry

/-- Syzygies of a finite free resolution are finite modules. -/
@[stacks 00NG "finite syzygy"]
instance finite (π : F ⟶ moduleSingle R M) [IsNoetherianRing R] [Module.Finite R M]
    [IsFiniteFreeResolution π] (n : ℕ) : Module.Finite R (syzygy π n) := sorry

end Syzygy

end ChainComplex
