/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Presheaf.Cech.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Coordinate formulas for Čech complexes

This file gives finite-intersection coordinates and alternating differential formulas for
presheaf Čech complexes.
-/

@[expose] public section

open CategoryTheory Opposite TopCat.Presheaf TopologicalSpace HomologicalComplex
open CategoryTheory.Limits
open scoped BigOperators ZeroObject

noncomputable section

universe u v

namespace TopCat.Presheaf.Cech

variable {X : TopCat.{u}} {ι : Type v}

/- Coordinate formulas are kept separate from the ordinary Čech complex owner so that ordered
intersections and alternating differentials can be imported independently. -/

/-- The open obtained by intersecting a finite tuple of members of an indexed family. -/
@[stacks 01EF "finite Cech intersections"]
abbrev intersection (𝒰 : ι → Opens X) {n : ℕ} (σ : Fin n → ι) : Opens X :=
  ⨅ a, 𝒰 (σ a)

/-- The inclusion of a finite Cech intersection into the intersection with one index omitted. -/
theorem intersection_le_succAbove (𝒰 : ι → Opens X) {n : ℕ}
    (σ : Fin (n + 1) → ι) (j : Fin (n + 1)) :
    intersection 𝒰 σ ≤ intersection 𝒰 (σ ∘ j.succAboveEmb) := sorry

/-- The degree-`p` tuplewise group of sections for a family of opens. -/
@[stacks 01EF "tuplewise Cech term"]
abbrev term (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    AddCommGrpCat.{max u v} :=
  AddCommGrpCat.of (∀ σ : Fin (p + 1) → ι, F.obj (op (intersection 𝒰 σ)))

/-- Restriction from a deleted tuple to the full tuple. -/
@[stacks 01EE "Cech restriction coordinate"]
abbrev restriction (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) {n : ℕ}
    (σ : Fin (n + 1) → ι) (j : Fin (n + 1)) :
    F.obj (op (intersection 𝒰 (σ ∘ j.succAboveEmb))) ⟶ F.obj (op (intersection 𝒰 σ)) :=
  F.map (homOfLE (intersection_le_succAbove 𝒰 σ j)).op

/-- The explicit alternating-sum function underlying the Cech differential. -/
@[stacks 01EE "tuplewise Cech differential formula"]
def differentialToFun (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    term 𝒰 F p → term 𝒰 F (p + 1) :=
  fun s σ ↦ ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
    restriction 𝒰 F σ j (s (σ ∘ j.succAboveEmb))

/-- Additivity of the explicit alternating-sum function. -/
theorem differentialToFun_map_add (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s t : term 𝒰 F p) :
    differentialToFun 𝒰 F p (s + t) =
      differentialToFun 𝒰 F p s + differentialToFun 𝒰 F p t := sorry

/-- The tuplewise Cech differential as an additive-group morphism. -/
@[stacks 01EF "tuplewise Cech differential"]
abbrev differential (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    term 𝒰 F p ⟶ term 𝒰 F (p + 1) :=
  AddCommGrpCat.ofHom (AddMonoidHom.mk' (differentialToFun 𝒰 F p)
    (differentialToFun_map_add 𝒰 F p))

/-- Applying the tuplewise differential exposes its underlying alternating-sum function. -/
@[simp, stacks 01EE "tuplewise Cech differential computation"]
theorem differential_apply (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) (s : term 𝒰 F p) :
    differential 𝒰 F p s = differentialToFun 𝒰 F p s := sorry

/-- Two successive tuplewise Cech differentials compose to zero. -/
theorem differential_comp (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    differential 𝒰 F p ≫ differential 𝒰 F (p + 1) = 0 := sorry


end TopCat.Presheaf.Cech

end
