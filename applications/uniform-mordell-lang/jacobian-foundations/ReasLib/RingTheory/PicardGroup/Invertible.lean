module

public import Mathlib.CategoryTheory.Core
public import Mathlib.RingTheory.PicardGroup
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import ReasLib.RingTheory.Flatness.LocallyFree.Finite
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Invertible modules and rank one

This module connects the categorical notion of a tensor-invertible object in `ModuleCat R` with
Mathlib's `Module.Invertible` predicate and finite local freeness of rank `1`. It also exposes the
dual module as the canonical value of any chosen tensor inverse.

@stack 0B8H
@stack 0B8I
-/

open CategoryTheory MonoidalCategory

universe u v w

namespace Module

namespace Invertible

section RankOne

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- An invertible module is canonically finite locally free of rank `1`. This is the only global
instance direction; the converse remains an explicit constructor to avoid an instance loop. -/
@[stacks 0B8I "invertible modules are finite locally free of rank one"]
instance instFiniteLocallyFreeOfRankOne [Module.Invertible R M] :
    Module.FiniteLocallyFreeOfRank R M 1 := sorry
-- Proof strategy: Mathlib's invertibility instance supplies `Module.Finite R M` and
-- `Module.Projective R M`; use `Module.FiniteLocallyFree.iff_finiteProjective` to obtain a standard
-- open finite-free cover.  Base-change the contraction equivalence to each localization.  On a
-- free localized module, `Module.Invertible.finrank_eq_one` identifies the chosen basis cardinal
-- with `1`; reindex the basis by `Fin 1` and package the same cover as
-- `Module.FiniteLocallyFreeOfRank R M 1`.

/-- A finite locally free module of rank `1` is invertible. -/
@[stacks 0B8I "finite locally free modules of rank one are invertible"]
theorem of_finiteLocallyFreeOfRank_one [Module.FiniteLocallyFreeOfRank R M 1] :
    Module.Invertible R M := sorry
-- Proof strategy: unfold `Module.Invertible` to the bijectivity of `contractLeft R M`.  Use the
-- standard-open cover from `Module.FiniteLocallyFreeOfRank.exists_standardOpen_cover` and the
-- local criterion for bijectivity of a linear map between finite modules.  After localization,
-- transport along the supplied equivalence with `Fin 1 → Localization.Away f`; contraction is
-- the ordinary evaluation pairing of a free rank-one module and is a linear equivalence.  The
-- cover spans `⊤`, so the localized bijectivity statements glue to the required global one.

/-- Invertibility is equivalent to finite local freeness of rank `1`. -/
@[stacks 0B8I "invertible iff finite locally free of rank one"]
theorem iff_finiteLocallyFreeOfRank_one :
    Module.Invertible R M ↔ Module.FiniteLocallyFreeOfRank R M 1 := sorry
-- Proof strategy: the forward implication is the canonical
-- `instFiniteLocallyFreeOfRankOne`; the reverse implication is
-- `of_finiteLocallyFreeOfRank_one`, installed only locally while constructing the implication to
-- avoid an instance loop.

end RankOne

section TensorInverse

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- A chosen module `N` satisfying `M ⊗[R] N ≃ₗ[R] R` is canonically linearly equivalent to
`Module.Dual R M`. -/
@[stacks 0B8I "Lemma 15.118.2 (2): a tensor inverse is the dual module"]
noncomputable def tensorInverseEquivDual (e : TensorProduct R M N ≃ₗ[R] R) :
    N ≃ₗ[R] Module.Dual R M :=
  Module.Invertible.linearEquivDual (TensorProduct.comm R N M ≪≫ₗ e)

end TensorInverse

end Invertible

end Module

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- The categorical tensor-invertibility predicate on `ModuleCat R` agrees with Mathlib's
contraction-map predicate `Module.Invertible`. -/
@[stacks 0B8H "Module-specific form of Definition 15.118.1"]
theorem isInvertibleObject_iff_invertible (M : ModuleCat R) :
    isInvertibleObject M ↔ Module.Invertible R M := sorry
-- Proof strategy: use
-- `MonoidalCategory.isInvertibleObject.iff_exists_rightTensorInverse`.  In the forward direction,
-- turn the categorical isomorphism `M ⊗ N ≅ 𝟙_ (ModuleCat R)` into the corresponding linear
-- equivalence and apply `Module.Invertible.left`.  In the reverse direction, take
-- `Module.Dual R M` as the inverse, compose `TensorProduct.comm` with
-- `Module.Invertible.linearEquiv R M`, convert that linear equivalence to a `ModuleCat` isomorphism,
-- and apply the same one-sided tensor-inverse criterion.

/-- A module is a trivial tensor-invertible object exactly when it is linearly equivalent to the
base ring. -/
@[stacks 0B8H "Trivial-module form of Definition 15.118.1"]
theorem isUnitObject_iff_linearEquiv (M : ModuleCat R) :
    isUnitObject M ↔ Nonempty (M ≃ₗ[R] R) := sorry
-- Proof strategy: unfold `MonoidalCategory.isUnitObject`; the monoidal unit of `ModuleCat R` is
-- the regular module `R`.  Convert in both directions with `ModuleCat.linearEquivIsoModuleIso`
-- (and its underlying-linear-equivalence projection), then package or eliminate `Nonempty`.

/-- The full subcategory of tensor-invertible `R`-modules. -/
@[stacks 0B8H "subcategory of invertible modules"]
abbrev Invertible (R : Type u) [CommRing R] : Type (u + 1) :=
    ObjectProperty.FullSubcategory (isInvertibleObject (C := ModuleCat R))

namespace Invertible

/-- The core groupoid of tensor-invertible `R`-modules. -/
@[stacks 0B8H "core groupoid of invertible modules"]
abbrev Core (R : Type u) [CommRing R] : Type (u + 1) :=
    CategoryTheory.Core (ModuleCat.Invertible R)

/-- Finite local freeness of rank `1`, categorical tensor invertibility, and the existence of a
one-sided tensor inverse are equivalent for an `R`-module. -/
@[stacks 0B8I "Lemma 15.118.2 (1): equivalent criteria for an invertible module"]
theorem tfae (M : ModuleCat R) :
    List.TFAE
      [ Module.FiniteLocallyFreeOfRank R M 1
      , isInvertibleObject M
      , ∃ N : ModuleCat R, Nonempty (M ⊗ N ≅ 𝟙_ (ModuleCat R))
      ] := sorry
-- Proof strategy: prove clause `(1) ↔ (2)` by composing
-- `Module.Invertible.iff_finiteLocallyFreeOfRank_one` with
-- `ModuleCat.isInvertibleObject_iff_invertible`.  Prove clause `(2) ↔ (3)` with the braided
-- monoidal theorem `MonoidalCategory.isInvertibleObject.iff_exists_rightTensorInverse`, then close
-- the three-way equivalence using `List.TFAE`.

end Invertible

end ModuleCat

end
