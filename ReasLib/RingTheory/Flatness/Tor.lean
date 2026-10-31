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
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Flatness.IdealTensor
public import ReasLib.Algebra.Category.ModuleCat.Tor.Ideal

/-!
# Flatness Criteria Through `Tor`

@stack 00M5
@stack 051C

This leaf owns the `Tor`-vanishing criteria for `Module.Flat`.  The derived-functor expressions
remain explicit, while the declarations live with the property they characterize rather than in a
particular categorical construction namespace.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace Module.Flat

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

/-- A flat module has vanishing `Tor_{n + 1}` against every module. -/
@[stacks 00M5 "flatness and Tor vanishing"]
theorem isZero_tor_succ (hM : Module.Flat R M) (n : ℕ) (N : ModuleCat R) :
    IsZero
      (((CategoryTheory.Tor (ModuleCat R) (n + 1)).obj (ModuleCat.of R M)).obj N) := by
  letI : Module.Flat R M := hM
  let F := (tensoringLeft (ModuleCat R)).obj (ModuleCat.of R M)
  let P := CategoryTheory.projectiveResolution N
  refine IsZero.of_iso ?_ (P.isoLeftDerivedObj F (n + 1))
  change IsZero (((F.mapHomologicalComplex _).obj P.complex).homology (n + 1))
  have hEx : (F.mapHomologicalComplex _).obj P.complex |>.ExactAt (n + 1) := by
    exact (P.complex_exactAt_succ n).map F
  exact hEx.isZero_homology

/-- A module is flat exactly when all positive-degree `Tor` objects against modules in the common
universe vanish. -/
@[stacks 00M5 "flatness and Tor vanishing"]
theorem iff_isZero_tor_succ :
    Module.Flat R M ↔ ∀ n : ℕ, ∀ N : ModuleCat R,
      IsZero
        (((CategoryTheory.Tor (ModuleCat R) (n + 1)).obj (ModuleCat.of R M)).obj N) := by
  constructor
  · intro hM n N
    exact isZero_tor_succ hM n N
  · intro h
    apply (Module.Flat.iff_lift_lsmul_comp_subtype_injective (R := R) (M := M)).2
    intro I hI
    simpa [Ideal.tensorMul] using
      (CategoryTheory.ModuleCat.Tor.isZero_oneQuotient_iff (M := M) I).1
        (h 0 (ModuleCat.of R (R ⧸ I)))

/-- A module is flat exactly when its first `Tor` object vanishes against every module in the
common universe. -/
@[stacks 00M5 "flatness and Tor vanishing"]
theorem iff_isZero_tor_one :
    Module.Flat R M ↔ ∀ N : ModuleCat R,
      IsZero (((CategoryTheory.Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj N) := by
  constructor
  · intro hM N
    simpa using isZero_tor_succ hM 0 N
  · intro h
    apply (Module.Flat.iff_lift_lsmul_comp_subtype_injective (R := R) (M := M)).2
    intro I hI
    simpa [Ideal.tensorMul] using
      (CategoryTheory.ModuleCat.Tor.isZero_oneQuotient_iff (M := M) I).1
        (h (ModuleCat.of R (R ⧸ I)))

/-- A module is flat exactly when `Tor₁(M, R ⧸ I)` vanishes for every ideal. -/
@[stacks 00M5 "flatness and Tor vanishing"]
theorem iff_isZero_tor_one_quotient :
    Module.Flat R M ↔ ∀ I : Ideal R,
      IsZero
        (((CategoryTheory.Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj
          (ModuleCat.of R (R ⧸ I))) := by
  constructor
  · intro hM I
    simpa using isZero_tor_succ hM 0 (ModuleCat.of R (R ⧸ I))
  · intro h
    apply (Module.Flat.iff_lift_lsmul_comp_subtype_injective (R := R) (M := M)).2
    intro I hI
    simpa [Ideal.tensorMul] using
      (CategoryTheory.ModuleCat.Tor.isZero_oneQuotient_iff (M := M) I).1 (h I)

/-- A module is flat exactly when `Tor₁(M, R ⧸ I)` vanishes for every finitely generated ideal.
-/
@[stacks 00M5 "flatness and Tor vanishing"]
theorem iff_isZero_tor_one_quotient_of_fg :
    Module.Flat R M ↔ ∀ I : Ideal R, I.FG →
      IsZero
        (((CategoryTheory.Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj
          (ModuleCat.of R (R ⧸ I))) := by
  constructor
  · intro hM I hI
    apply (CategoryTheory.ModuleCat.Tor.isZero_oneQuotient_iff (M := M) I).2
    simpa [Ideal.tensorMul] using
      ((Module.Flat.iff_lift_lsmul_comp_subtype_injective (R := R) (M := M)).1 hM
        (I := I) hI)
  · intro h
    apply (Module.Flat.iff_lift_lsmul_comp_subtype_injective (R := R) (M := M)).2
    intro I hI
    apply (CategoryTheory.ModuleCat.Tor.isZero_oneQuotient_iff (M := M) I).1 (h I hI)

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
              (ModuleCat.of R (R ⧸ I))) ] := by
  tfae_have 1 ↔ 2 := iff_isZero_tor_succ
  tfae_have 2 → 3 := by
    intro h N
    simpa using h 0 N
  tfae_have 3 → 4 := by
    intro h I
    exact h (ModuleCat.of R (R ⧸ I))
  tfae_have 4 → 5 := by
    intro h I _
    exact h I
  tfae_have 5 → 1 :=
    (iff_isZero_tor_one_quotient_of_fg (R := R) (M := M)).mpr
  tfae_finish

end Module.Flat
