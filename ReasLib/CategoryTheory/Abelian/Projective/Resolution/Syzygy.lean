/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.ChainComplex.Bounded

/-!
# Syzygies of categorical projective resolutions

This leaf owns the resolution-independent syzygy objects attached to a chosen
`CategoryTheory.ProjectiveResolution`.  The kernels are taken in the ambient
abelian category, so the API is not tied to linear-map representatives in
`ModuleCat`.  Finite coordinate resolutions remain source-facing views.
-/

@[expose] public section

noncomputable section

universe v u

namespace CategoryTheory

open Category Limits Projective

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {X : C}

namespace ProjectiveResolution

/- The object-level owner is deliberately independent of any module presentation. -/

/-- The `n`th syzygy of a chosen projective resolution.  Degree `0` is the target,
degree `1` is the augmentation kernel, and later degrees are kernels of the
successive differentials. -/
@[stacks 0CXC "categorical syzygy of a projective resolution"]
noncomputable def syzygy (P : ProjectiveResolution X) : ℕ → C
  | 0 => X
  | 1 => kernel (P.π.f 0)
  | n + 2 => kernel (P.complex.d (n + 1) n)

/-- The zeroth syzygy is the resolved object. -/
@[simp, stacks 0CXC "zeroth syzygy"]
theorem syzygy_zero (P : ProjectiveResolution X) :
    P.syzygy 0 = X := sorry
/- Proof strategy: unfold `syzygy` at index `0`. -/

/-- The first syzygy is the kernel of the augmentation. -/
@[simp, stacks 0CXC "first syzygy"]
theorem syzygy_one (P : ProjectiveResolution X) :
    P.syzygy 1 = kernel (P.π.f 0) := sorry
/- Proof strategy: unfold `syzygy` at index `1`. -/

/-- A higher syzygy is the kernel of the corresponding differential. -/
@[simp, stacks 0CXC "successive syzygy"]
theorem syzygy_succ_succ (P : ProjectiveResolution X) (n : ℕ) :
    P.syzygy (n + 2) = kernel (P.complex.d (n + 1) n) := sorry
/- Proof strategy: unfold `syzygy` in the successor-successor branch. -/

/-- The inclusion of the `(n + 1)`st syzygy into the `n`th resolving term. -/
@[stacks 0CXC "syzygy inclusion"]
noncomputable def inclusion (P : ProjectiveResolution X) (n : ℕ) :
    P.syzygy (n + 1) ⟶ P.complex.X n :=
  match n with
  | 0 => kernel.ι (P.π.f 0)
  | n + 1 => kernel.ι (P.complex.d (n + 1) n)

/-- The canonical map from the `n`th resolving term to its preceding syzygy. -/
@[stacks 0CXC "map from a resolving term to its syzygy"]
noncomputable def toSyzygy (P : ProjectiveResolution X) :
    (n : ℕ) → P.complex.X n ⟶ P.syzygy n
  | 0 => P.π.f 0
  | 1 => kernel.lift (P.π.f 0) (P.complex.d 1 0) P.complex_d_comp_π_f_zero
  | n + 2 =>
      kernel.lift (P.complex.d (n + 1) n) (P.complex.d (n + 2) (n + 1))
        (P.complex.d_comp_d (n + 2) (n + 1) n)

/-- The syzygy inclusion followed by the map to the preceding syzygy is zero. -/
@[stacks 0CXC "syzygy inclusion composition"]
theorem inclusion_comp_toSyzygy (P : ProjectiveResolution X) (n : ℕ) :
    P.inclusion n ≫ P.toSyzygy n = 0 := sorry
/- Proof strategy: split on `n`; use `kernel.condition` in degree zero and the
chain-complex differential relation in the positive cases. -/

/-- The two consecutive syzygy maps form their canonical short complex. -/
@[stacks 0CXC "short complex of consecutive syzygies"]
noncomputable def shortComplex (P : ProjectiveResolution X) (n : ℕ) :
    ShortComplex C :=
  ShortComplex.mk (P.inclusion n) (P.toSyzygy n) (P.inclusion_comp_toSyzygy n)

/-- Consecutive syzygies form a short exact row in a projective resolution. -/
@[stacks 0CXC "short exact syzygy row"]
theorem shortExact (P : ProjectiveResolution X) (n : ℕ) :
    (P.shortComplex n).ShortExact := sorry
/- Proof strategy: identify the row with the augmentation exact row for `n = 0`
and with `P.exact_succ` after factoring the kernel maps for positive `n`. -/

/-- The projective-resolution view of the shared upper support bound on its underlying chain
complex. -/
@[stacks 0CXC "bounded projective resolution"]
abbrev IsBoundedLE (P : ProjectiveResolution X) (d : ℕ) : Prop :=
  ChainComplex.IsBoundedLE P.complex d

/-- An object admits a projective resolution of length at most `d`. -/
@[stacks 0CXC "projective resolution of bounded length"]
def HasLengthLE (X : C) (d : ℕ) : Prop :=
  ∃ P : ProjectiveResolution X, P.IsBoundedLE d

/-- A bounded projective-resolution witness gives the corresponding projective-dimension bound.

Unlike the TFAE below, this implication needs no ambient `HasProjectiveResolution X` instance:
the required resolution is already explicit in `HasLengthLE X d`. -/
@[stacks 0CXC "projective dimension from a bounded projective resolution"]
theorem HasLengthLE.hasProjectiveDimensionLE {d : ℕ}
    (hX : HasLengthLE X d) :
    HasProjectiveDimensionLE X d := sorry

/-- The projective-dimension bound is equivalent to projectivity of the corresponding syzygy. -/
@[stacks 0CXC "projective syzygy criterion"]
theorem projective_syzygy_iff (P : ProjectiveResolution X) (d : ℕ) :
    Projective (P.syzygy d) ↔ HasProjectiveDimensionLE X d := sorry
/- Proof strategy: induct on `d` and apply the projective-dimension shift across
the short exact syzygy rows. -/

/-- Projective dimension shifts along the syzygy tower. -/
@[stacks 0CXC "projective-dimension syzygy shift"]
theorem hasProjectiveDimensionLE_syzygy_iff (P : ProjectiveResolution X)
    (n d : ℕ) :
    HasProjectiveDimensionLE (P.syzygy n) d ↔
      HasProjectiveDimensionLE X (n + d) := sorry
/- Proof strategy: induct on `n`, using the projective middle term of each
`shortExact` row and the three canonical short-exact dimension inequalities. -/

/-- A projective-dimension bound forces the corresponding syzygy to be projective. -/
@[stacks 0CXC "projective syzygy from projective dimension"]
theorem syzygy_projective_of_hasProjectiveDimensionLE
    (P : ProjectiveResolution X) {d : ℕ}
    (hX : HasProjectiveDimensionLE X d) : Projective (P.syzygy d) := sorry
/- Proof strategy: use `projective_syzygy_iff P d` in the forward direction. -/

/-- A projective syzygy gives the corresponding projective-dimension bound. -/
@[stacks 0CXC "projective dimension from a projective syzygy"]
theorem hasProjectiveDimensionLE_of_projective_syzygy
    (P : ProjectiveResolution X) {d : ℕ}
    (hP : Projective (P.syzygy d)) : HasProjectiveDimensionLE X d := sorry
/- Proof strategy: use `projective_syzygy_iff P d` in the reverse direction. -/

/-- The bounded-resolution, syzygy, and projective-dimension formulations are equivalent. -/
@[stacks 0CXC "projective dimension and bounded resolutions"]
theorem projectiveDimensionLE_tfae [HasProjectiveResolution X] (d : ℕ) :
    List.TFAE
      [ HasProjectiveDimensionLE X d,
        HasLengthLE X d,
        ∃ P : ProjectiveResolution X, Projective (P.syzygy d),
        ∀ P : ProjectiveResolution X, Projective (P.syzygy d) ] := sorry
/- Proof strategy: combine the bounded truncation construction with the syzygy
criterion, then use the chosen projective resolution for the existential clause. -/

end ProjectiveResolution

end CategoryTheory
