/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Tor.Exact

/-!
# Scalar actions on `Tor`

This leaf separates compatibility of module scalar multiplication with the
derived `Tor` functor from the exact-sequence consequences that use it.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.ModuleCat.Tor

variable {R : Type u} [CommRing R]

/-- Stacks 0H7P: the module-first `Tor` map induced by scalar multiplication on its variable is
the corresponding scalar multiple of the identity morphism. -/
@[stacks 0H7P "Tor scalar action"]
theorem map_lsmul_eq_smul
    (M : ModuleCat R) {K : Type u} [AddCommGroup K] [Module R K]
    (a : R) (n : ℕ) :
    ((CategoryTheory.Tor (ModuleCat R) n).obj M).map
        (ModuleCat.ofHom (LinearMap.lsmul R K a)) =
      a • 𝟙 (((CategoryTheory.Tor (ModuleCat R) n).obj M).obj (ModuleCat.of R K)) := sorry

/-- Stacks 0H7P: scalar multiplication is injective on degree-`n` module-first `Tor` when the
adjacent `Tor` groups of its kernel and cokernel vanish. -/
@[stacks 0H7P "Tor scalar injectivity"]
theorem smul_injective_of_isZero_ker_cokernel
    (M : ModuleCat R) {K : Type u} [AddCommGroup K] [Module R K]
    (a : R) (n : ℕ)
    (hker :
      IsZero (((CategoryTheory.Tor (ModuleCat R) n).obj M).obj
        (ModuleCat.of R (LinearMap.ker (LinearMap.lsmul R K a)))))
    (hcoker :
      IsZero (((CategoryTheory.Tor (ModuleCat R) (n + 1)).obj M).obj
        (ModuleCat.of R (K ⧸ LinearMap.range (LinearMap.lsmul R K a))))) :
    Function.Injective
      (fun t : (((CategoryTheory.Tor (ModuleCat R) n).obj M).obj (ModuleCat.of R K)) ↦ a • t) := sorry

end CategoryTheory.ModuleCat.Tor
