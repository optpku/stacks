/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Horseshoes of Projective Resolutions of Modules

This leaf owns explicit degreewise split horseshoe rows for short exact
sequences in `ModuleCat`. It records a supplied middle resolution and never
chooses a horseshoe from an existence theorem; this keeps the non-Prop data
safe for later derived-functor constructions.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.ProjectiveResolution

section

variable {R : Type u} [Ring R]

/-- A degreewise split projective horseshoe over a short exact sequence of
`R`-modules. The outer resolutions are the canonical projective resolutions
of the endpoints, while `middle` is supplied explicitly. -/
@[stacks 00M0 "projective horseshoe for Tor"]
structure Horseshoe (S : ShortComplex (ModuleCat R)) where
  /-- The source row is short exact. -/
  sourceShortExact : S.ShortExact
  /-- A projective resolution of the middle term. -/
  middle : CategoryTheory.ProjectiveResolution S.X₂
  /-- The comparison from the left endpoint resolution to the middle one. -/
  iota : (CategoryTheory.projectiveResolution S.X₁).complex ⟶ middle.complex
  /-- The comparison from the middle resolution to the right endpoint resolution. -/
  pi : middle.complex ⟶ (CategoryTheory.projectiveResolution S.X₃).complex
  /-- The two resolution comparisons compose to zero. -/
  zero : iota ≫ pi = 0
  /-- The left comparison lifts `S.f` through the two augmentations. -/
  iota_augment :
    iota ≫ middle.π =
      (CategoryTheory.projectiveResolution S.X₁).π ≫
        (ChainComplex.single₀ (ModuleCat R)).map S.f
  /-- The right comparison lifts `S.g` through the two augmentations. -/
  pi_augment :
    pi ≫ (CategoryTheory.projectiveResolution S.X₃).π =
      middle.π ≫ (ChainComplex.single₀ (ModuleCat R)).map S.g
  /-- Every degree of the resolving row is split exact. -/
  splitting : ∀ n : ℕ,
    ((ShortComplex.mk iota pi zero).map
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n)).Splitting

end

namespace Horseshoe

section

variable {R : Type u} [Ring R]
variable {S : ShortComplex (ModuleCat R)}

/-- The short complex of projective resolutions underlying a horseshoe. -/
@[stacks 00M0 "projective horseshoe for Tor"]
def row (H : Horseshoe S) : ShortComplex (ChainComplex (ModuleCat R) ℕ) :=
  ShortComplex.mk H.iota H.pi H.zero

/-- The underlying resolving row of a horseshoe is short exact. -/
@[stacks 00M0 "projective horseshoe for Tor"]
theorem row_shortExact (H : Horseshoe S) : H.row.ShortExact := sorry

end

section Tensor

variable {R : Type u} [CommRing R]
variable {S : ShortComplex (ModuleCat R)}

/-- Tensoring a horseshoe row on the right by `M`, degreewise. -/
@[stacks 00M0 "Tor exact sequence"]
noncomputable def tensorRightRow (H : Horseshoe S) (M : ModuleCat R) :
    ShortComplex (ChainComplex (ModuleCat R) ℕ) :=
  H.row.map
    ((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex (ComplexShape.down ℕ))

/-- Tensoring a degreewise split horseshoe row on the right preserves its
short exactness. -/
@[stacks 00M0 "Tor exact sequence"]
theorem tensorRightRow_shortExact (H : Horseshoe S) (M : ModuleCat R) :
    (H.tensorRightRow M).ShortExact := sorry

end Tensor

end Horseshoe

end CategoryTheory.ModuleCat.ProjectiveResolution
