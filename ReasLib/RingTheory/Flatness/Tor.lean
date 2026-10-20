/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Flatness.IdealTensor

/-!
# Flatness Criteria Through `Tor`

@stack 00M5
@stack 051C

This leaf owns the `Tor`-vanishing criteria for `Module.Flat`.  The derived-functor expressions
remain explicit, while the declarations live with the property they characterize rather than in a
particular categorical construction namespace.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Module.Flat

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

/-- A flat module has vanishing `Tor_{n + 1}` against every module. -/
@[stacks 00M5 "flatness and Tor vanishing"]
theorem isZero_tor_succ (hM : Module.Flat R M) (n : ℕ) (N : ModuleCat R) :
    IsZero
      (((CategoryTheory.Tor (ModuleCat R) (n + 1)).obj (ModuleCat.of R M)).obj N) := sorry

/-- A module is flat exactly when all positive-degree `Tor` objects against modules in the common
universe vanish. -/
@[stacks 00M5 "flatness and Tor vanishing"]
theorem iff_isZero_tor_succ :
    Module.Flat R M ↔ ∀ n : ℕ, ∀ N : ModuleCat R,
      IsZero
        (((CategoryTheory.Tor (ModuleCat R) (n + 1)).obj (ModuleCat.of R M)).obj N) := sorry

/-- A module is flat exactly when its first `Tor` object vanishes against every module in the
common universe. -/
@[stacks 00M5 "flatness and Tor vanishing"]
theorem iff_isZero_tor_one :
    Module.Flat R M ↔ ∀ N : ModuleCat R,
      IsZero (((CategoryTheory.Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj N) := sorry

/-- A module is flat exactly when `Tor₁(M, R ⧸ I)` vanishes for every ideal. -/
@[stacks 00M5 "flatness and Tor vanishing"]
theorem iff_isZero_tor_one_quotient :
    Module.Flat R M ↔ ∀ I : Ideal R,
      IsZero
        (((CategoryTheory.Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj
          (ModuleCat.of R (R ⧸ I))) := sorry

/-- A module is flat exactly when `Tor₁(M, R ⧸ I)` vanishes for every finitely generated ideal.
-/
@[stacks 00M5 "flatness and Tor vanishing"]
theorem iff_isZero_tor_one_quotient_of_fg :
    Module.Flat R M ↔ ∀ I : Ideal R, I.FG →
      IsZero
        (((CategoryTheory.Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj
          (ModuleCat.of R (R ⧸ I))) := sorry

/-- Lemma 10.99.8 (1): quotient flatness modulo `I` together with vanishing of
`Tor₁^R(R ⧸ I, M)` gives quotient flatness modulo every positive power of `I`. -/
@[stacks 051C "(1)"]
theorem quotient_pow_of_quotient_flat_of_isZero_tor_one {I : Ideal R}
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)))
    (htor :
      IsZero
        (((CategoryTheory.Tor (ModuleCat R) 1).obj (ModuleCat.of R (R ⧸ I))).obj
          (ModuleCat.of R M)))
    (n : ℕ) (hn : 1 ≤ n) :
    Module.Flat (R ⧸ I ^ n) (M ⧸ (I ^ n • ⊤ : Submodule R M)) := sorry

/-- Lemma 10.99.8 (2): quotient flatness modulo `I` and vanishing of
`Tor₁^R(R ⧸ I, M)` force `Tor₁^R(N, M)` to vanish when a power of `I` annihilates `N`. -/
@[stacks 051C "(2)"]
theorem isZero_tor_one_of_annihilated_by_ideal_pow {I : Ideal R}
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)))
    (htor :
      IsZero
        (((CategoryTheory.Tor (ModuleCat R) 1).obj (ModuleCat.of R (R ⧸ I))).obj
          (ModuleCat.of R M)))
    {N : Type u} [AddCommGroup N] [Module R N] (n : ℕ)
    (hN : I ^ n ≤ Module.annihilator R N) :
    IsZero
      (((CategoryTheory.Tor (ModuleCat R) 1).obj (ModuleCat.of R N)).obj
        (ModuleCat.of R M)) := sorry

/-- Lemma 10.99.8 (3): quotient flatness modulo a nilpotent ideal and vanishing of
`Tor₁^R(R ⧸ I, M)` imply flatness of `M`. -/
@[stacks 051C "(3)"]
theorem of_isNilpotent_ideal_of_quotient_flat_of_isZero_tor_one {I : Ideal R}
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M)))
    (htor :
      IsZero
        (((CategoryTheory.Tor (ModuleCat R) 1).obj (ModuleCat.of R (R ⧸ I))).obj
          (ModuleCat.of R M)))
    (hI : IsNilpotent I) :
    Module.Flat R M := sorry

/-- The standard five equivalent `Tor`-vanishing criteria for flatness. -/
@[stacks 00M5 "flatness and Tor vanishing"]
theorem tor_tfae :
    List.TFAE
      [ Module.Flat R M,
        ∀ n : ℕ, ∀ N : ModuleCat R,
          IsZero
            (((CategoryTheory.Tor (ModuleCat R) (n + 1)).obj
              (ModuleCat.of R M)).obj N),
        ∀ N : ModuleCat R,
          IsZero
            (((CategoryTheory.Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj N),
        ∀ I : Ideal R,
          IsZero
            (((CategoryTheory.Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj
              (ModuleCat.of R (R ⧸ I))),
        ∀ I : Ideal R, I.FG →
          IsZero
            (((CategoryTheory.Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj
              (ModuleCat.of R (R ⧸ I))) ] := sorry

end Module.Flat
