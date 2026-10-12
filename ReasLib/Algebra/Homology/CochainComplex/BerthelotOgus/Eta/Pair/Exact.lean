/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Pair

/-!
# The exact row associated to the visible-power eta pair

The pair map `(1, d)` is the kernel of the complementary map `(d, -1)`.  Restricting the latter
to its range gives a canonical short exact row whose splitting is controlled by projectivity of
that range.
@stack 0F7W
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CochainComplex.BerthelotOgus.Nat.Pair

variable {A : Type u} [CommRing A]

/-- The target `f^n K^(n+1)` of the complementary map `(d, -1)`. -/
def deltaTarget (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    Submodule A (K.X (n + 1)) :=
  principalIdeal (f ^ n) • (⊤ : Submodule A (K.X (n + 1)))

/-- The differential sends the first visible power submodule into `deltaTarget`. -/
theorem differential_mem_deltaTarget
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    (x : powerSubmodule f K n) : (K.d n (n + 1)).hom x ∈ deltaTarget f K n := sorry

/-- The next visible power submodule is contained in `deltaTarget`. -/
theorem nextPowerSubmodule_le_deltaTarget
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    nextPowerSubmodule f K n ≤ deltaTarget f K n := sorry

/-- The differential on the first visible power, with codomain restricted to `deltaTarget`. -/
def differentialToDelta
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    powerSubmodule f K n →ₗ[A] deltaTarget f K n :=
  ((K.d n (n + 1)).hom.comp (powerSubmodule f K n).subtype).codRestrict
    (deltaTarget f K n) (differential_mem_deltaTarget f K n)

/-- The complementary map `(d, -1)` on the two visible power submodules. -/
@[stacks 0F7W "complementary map for the Berthelot-Ogus eta pair"]
def deltaLinear (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    powerSubmodule f K n × nextPowerSubmodule f K n →ₗ[A] deltaTarget f K n :=
  ((differentialToDelta f K n).comp
      (LinearMap.fst A (powerSubmodule f K n) (nextPowerSubmodule f K n))) -
    ((Submodule.inclusion (nextPowerSubmodule_le_deltaTarget f K n)).comp
      (LinearMap.snd A (powerSubmodule f K n) (nextPowerSubmodule f K n)))

/-- The complementary map vanishes after the visible-power pair map. -/
theorem deltaLinear_comp_pairLinear
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    (deltaLinear f K n).comp (pairLinear f K n) = 0 := sorry

/-- The kernel of `(d, -1)` is the range of the visible-power pair map `(1, d)`. -/
theorem ker_deltaLinear_eq_range_pairLinear
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    LinearMap.ker (deltaLinear f K n) = LinearMap.range (pairLinear f K n) := sorry

/-- The range-restricted complementary map vanishes after the visible-power pair map. -/
theorem deltaLinear_rangeRestrict_comp_pairLinear
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    (deltaLinear f K n).rangeRestrict.comp (pairLinear f K n) = 0 := sorry

/-- The canonical exact row from an eta term through the two visible power submodules to the
range of `(d, -1)`. -/
@[stacks 0F7W "exact row for a Berthelot-Ogus eta term"]
def rangeShortComplex
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    ShortComplex (ModuleCat.{v} A) :=
  ShortComplex.mk
    (ModuleCat.ofHom (pairLinear f K n))
    (ModuleCat.ofHom (deltaLinear f K n).rangeRestrict)
    (congrArg ModuleCat.ofHom (deltaLinear_rangeRestrict_comp_pairLinear f K n))

/-- The canonical eta pair row is short exact. -/
theorem rangeShortComplex_shortExact
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    (rangeShortComplex f K n).ShortExact := sorry

/-- Projectivity of the complementary range splits the visible-power pair inclusion. -/
theorem pairLinear_isSplitMono_of_deltaRange_projective
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    [Module.Projective A (LinearMap.range (deltaLinear f K n))] :
    IsSplitMono (ModuleCat.ofHom (pairLinear f K n)) := sorry

end CochainComplex.BerthelotOgus.Nat.Pair
