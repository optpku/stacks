/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Abelian.Projective.Resolution.Syzygy

/-!
# Coordinate projective resolutions of bounded length

This leaf owns the coordinate presentation of a bounded projective resolution in `ModuleCat`.
It is deliberately separate from `CategoryTheory.ProjectiveResolution.HasLengthLE`: the latter
quantifies over a bundled projective resolution, while this owner exposes the finite `Fin`
sequence and its linear-map exactness clauses for module-theoretic applications.

The historical Chap10 name `HasFiniteProjectiveResolutionLengthLE` is only a compatibility view;
the coordinate owner itself does not assert finite generation.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.ModuleCat.ProjectiveResolution

variable {R : Type u} [Ring R]

namespace Coordinate

/-- A coordinate projective resolution of `M` has length at most `d`.

For `d = 0`, this is projectivity of `M`. For `d = n + 1`, it is a finite exact coordinate
sequence of projective terms `P i` ending in a surjective augmentation to `M`, with exact
consecutive maps and an injective top differential.
-/
@[stacks 0CXC "coordinate projective resolution of bounded length"]
def HasLengthLE (M : ModuleCat.{v} R) (d : ℕ) : Prop :=
  match d with
  | 0 => Projective M
  | n + 1 =>
      ∃ (P : Fin (n + 2) → ModuleCat.{v} R),
        (∀ i, Projective (P i)) ∧
          ∃ (δ : (i : Fin (n + 1)) → P i.succ ⟶ P i.castSucc)
            (π : P 0 ⟶ M),
            Function.Surjective π.hom ∧
              Function.Exact (δ 0).hom π.hom ∧
              (∀ i : Fin n, Function.Exact (δ i.succ).hom (δ i.castSucc).hom) ∧
                Function.Injective (δ (Fin.last n)).hom

/-- A coordinate projective resolution has length at most zero exactly when its target is projective.
-/
@[stacks 0CXC "zero-length coordinate projective resolution"]
theorem HasLengthLE.zero_iff (M : ModuleCat.{v} R) :
    HasLengthLE M 0 ↔ Projective M := sorry

/-- The positive-length coordinate predicate decomposes into a projective presentation and a
shorter coordinate resolution of its kernel.
-/
@[stacks 0CXC "successor decomposition of a coordinate projective resolution"]
theorem HasLengthLE.exists_projectivePresentation {M : ModuleCat.{v} R} {n : ℕ}
    (hM : HasLengthLE M (n + 1)) :
    ∃ (P₀ : ModuleCat.{v} R) (π : P₀ ⟶ M),
      Projective P₀ ∧
        Function.Surjective π.hom ∧
          HasLengthLE (ModuleCat.of R (LinearMap.ker π.hom)) n := sorry

/-- A projective presentation and a shorter kernel resolution extend to the successor length.
-/
@[stacks 0CXC "successor construction for a coordinate projective resolution"]
theorem HasLengthLE.succ_of_projectivePresentation {M : ModuleCat.{v} R}
    {P₀ : ModuleCat.{v} R} (π : P₀ ⟶ M) (hP₀ : Projective P₀)
    (hπ : Function.Surjective π.hom) {n : ℕ}
    (hker : HasLengthLE (ModuleCat.of R (LinearMap.ker π.hom)) n) :
    HasLengthLE M (n + 1) := sorry

/-- The positive-length coordinate predicate is equivalent to the projective-presentation
recurrence exposed by `HasLengthLE.exists_projectivePresentation` and
`HasLengthLE.succ_of_projectivePresentation`.
-/
@[stacks 0CXC "coordinate projective resolution successor recurrence"]
theorem HasLengthLE.succ_iff (M : ModuleCat.{v} R) (n : ℕ) :
    HasLengthLE M (n + 1) ↔
    ∃ (P₀ : ModuleCat.{v} R) (π : P₀ ⟶ M),
      Projective P₀ ∧
          Function.Surjective π.hom ∧
            HasLengthLE (ModuleCat.of R (LinearMap.ker π.hom)) n := sorry

/-- Stacks `0CXC`: a coordinate bounded projective resolution determines the canonical
categorical bounded-resolution predicate. -/
@[stacks 0CXC "coordinate-to-categorical bounded projective resolution"]
theorem HasLengthLE.toCanonical {M : ModuleCat.{v} R} {d : ℕ}
    (hM : HasLengthLE M d) :
    CategoryTheory.ProjectiveResolution.HasLengthLE M d := sorry

/-- Stacks `0CXC`: a canonical bounded projective resolution admits its finite coordinate
description in `ModuleCat`. -/
@[stacks 0CXC "categorical-to-coordinate bounded projective resolution"]
theorem HasLengthLE.ofCanonical {M : ModuleCat.{v} R} {d : ℕ}
    (hM : CategoryTheory.ProjectiveResolution.HasLengthLE M d) :
    HasLengthLE M d := sorry

/-- Stacks `0CXC`: a coordinate bounded projective resolution bounds the projective dimension of
its target. -/
@[stacks 0CXC "projective dimension from a coordinate bounded projective resolution"]
theorem HasLengthLE.hasProjectiveDimensionLE {M : ModuleCat.{v} R} {d : ℕ}
    (hM : HasLengthLE M d) :
    HasProjectiveDimensionLE M d := sorry

/-- Stacks `0CXC`: a projective-dimension bound yields a coordinate bounded projective resolution
once a projective resolution of the target is available.

The local `HasProjectiveResolution M` assumption is intentionally weaker than imposing
`Small.{v} R` or a global enough-projectives instance on `ModuleCat R`. -/
@[stacks 0CXC "coordinate bounded projective resolution from projective dimension"]
theorem HasLengthLE.of_hasProjectiveDimensionLE {M : ModuleCat.{v} R} {d : ℕ}
    [CategoryTheory.HasProjectiveResolution M] (hM : HasProjectiveDimensionLE M d) :
    HasLengthLE M d := sorry

end Coordinate

/-- Stacks `0CXC`: the augmentation row of a projective resolution is exact when viewed as a
pair of linear maps. -/
@[stacks 0CXC "projective-resolution augmentation exactness"]
theorem exact_zero_hom
    {M : ModuleCat.{v} R} (P : CategoryTheory.ProjectiveResolution M) :
    Function.Exact (P.complex.d 1 0).hom (P.π.f 0).hom := sorry

/-- Stacks `0CXC`: two consecutive differentials of a projective resolution are exact when
viewed as linear maps. -/
@[stacks 0CXC "projective-resolution differential exactness"]
theorem exact_succ_hom
    {M : ModuleCat.{v} R} (P : CategoryTheory.ProjectiveResolution M) (n : ℕ) :
    Function.Exact (P.complex.d (n + 2) (n + 1)).hom (P.complex.d (n + 1) n).hom := sorry

end CategoryTheory.ModuleCat.ProjectiveResolution
