/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Constant Rank for Finite Locally Free Module Sheaves

Fixed rank is owned at Mathlib's `SheafOfModules.LocalGeneratorsData` layer for modules over an
arbitrary sheaf of rings. Restriction and cover characterizations belong to ringed-site bridge
modules.
-/

@[expose] public section

open CategoryTheory Limits

universe u v w x

namespace SheafOfModules

namespace LocalGeneratorsData

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{w}}
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Local free-generator data has rank `r` when every local basis-indexing type is equivalent
to `Fin r`. This is the fixed-rank refinement of Mathlib's `IsLocallyFreeData`. -/
@[stacks 0409 "fixed-rank local-generator data"]
class IsFreeOfRank {M : SheafOfModules.{w} R}
    (q : M.LocalGeneratorsData.{x}) (r : ℕ) : Prop extends q.IsLocallyFreeData where
  /-- Every local basis has exactly `r` elements. -/
  equivFin (i : q.I) : Nonempty ((q.generators i).I ≃ Fin r)

/-- Fixed-rank local free data is equivalently local free data together with a rank equivalence
for every member of the chosen cover. -/
@[stacks 0409 "fixed-rank local-generator specification"]
theorem isFreeOfRank_iff {M : SheafOfModules.{w} R}
    (q : M.LocalGeneratorsData.{x}) (r : ℕ) :
    q.IsFreeOfRank r ↔
      q.IsLocallyFreeData ∧ ∀ i : q.I, Nonempty ((q.generators i).I ≃ Fin r) := sorry

/-- Fixed-rank local free data has finite generating families. -/
theorem IsFreeOfRank.isFiniteType {M : SheafOfModules.{w} R}
    (q : M.LocalGeneratorsData.{x}) (r : ℕ) [q.IsFreeOfRank r] : q.IsFiniteType := sorry

end LocalGeneratorsData

section Rank

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{w}}
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A module sheaf has finite local rank `r` when it admits Mathlib local-generator data which is
locally free of rank `r`. -/
@[stacks 0409 "(1)", stacks 01C6 "(3)"]
class IsFiniteLocallyFreeOfRank (r : ℕ) (M : SheafOfModules.{w} R) : Prop
    extends IsFiniteLocallyFree M where
  /-- A common rank-`r` local-free datum. -/
  exists_rank_data : ∃ q : M.LocalGeneratorsData.{u}, q.IsFreeOfRank r

/-- Finite local freeness of a fixed rank is closed under isomorphisms. -/
instance isFiniteLocallyFreeOfRank_isClosedUnderIsomorphisms (r : ℕ) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (IsFiniteLocallyFreeOfRank r : ObjectProperty (SheafOfModules.{w} R)) := sorry

/-- The defining local-generator description of finite local freeness of rank `r`. -/
@[stacks 0409 "local-generator specification", stacks 01C6 "(3), specification"]
theorem isFiniteLocallyFreeOfRank_iff (r : ℕ) (M : SheafOfModules.{w} R) :
    IsFiniteLocallyFreeOfRank r M ↔
      ∃ q : M.LocalGeneratorsData.{u}, q.IsFreeOfRank r := sorry

section Free

variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The free module sheaf on the standard `r`-element basis has finite local rank `r`. -/
instance free_isFiniteLocallyFreeOfRank (r : ℕ) :
    IsFiniteLocallyFreeOfRank r
      (free (R := R) (ULift.{w} (Fin r)) : SheafOfModules.{w} R) := sorry

end Free

/-- The structure module of a ring sheaf has finite local rank one. -/
instance unit_isFiniteLocallyFreeOfRankOne :
    IsFiniteLocallyFreeOfRank 1 (unit R : SheafOfModules.{w} R) := sorry

end Rank

namespace IsFiniteLocallyFreeOfRank

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{w}}
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Transport finite local freeness of fixed rank from the source of an isomorphism to its target.
-/
@[stacks 0409 "invariance under isomorphism"]
theorem of_iso {M N : SheafOfModules.{w} R} (e : M ≅ N) {r : ℕ}
    [IsFiniteLocallyFreeOfRank r M] :
    IsFiniteLocallyFreeOfRank r N := sorry

/-- Finite local freeness of a fixed rank is invariant under isomorphism. -/
theorem iff_of_iso {M N : SheafOfModules.{w} R} (e : M ≅ N) (r : ℕ) :
    IsFiniteLocallyFreeOfRank r M ↔ IsFiniteLocallyFreeOfRank r N := sorry

end IsFiniteLocallyFreeOfRank

end SheafOfModules
