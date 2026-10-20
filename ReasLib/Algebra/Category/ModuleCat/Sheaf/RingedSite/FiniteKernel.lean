/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.LocalProperties.Covers
import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local finite-kernel presentations

This file owns the reusable local shape "a kernel of a map between finite direct sums of copies
of one module sheaf".  Internal Hom is one source of this shape, but the predicate itself is
independent of internal Hom and of ringed spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.FiniteKernel

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{w}}
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A module sheaf `H` is locally a kernel between finite biproducts of copies of `G` when
some cover of the top has such a presentation on every member. -/
@[stacks 01CQ "local finite-kernel model"]
def IsLocal (G H : SheafOfModules.{w} R) : Prop :=
  ∃ (I : Type u) (U : I → C), J.CoversTop U ∧
    ∀ i : I, ∃ (m n : ℕ)
      (φ : (∏ᶜ fun _ : Fin m ↦ G.over (U i)) ⟶
        (∏ᶜ fun _ : Fin n ↦ G.over (U i))),
        Nonempty (H.over (U i) ≅ kernel φ)

/-- A local finite-kernel presentation is invariant under isomorphism of the presented module
sheaf. -/
theorem ofIso {G H K : SheafOfModules.{w} R}
    (h : IsLocal G H) (e : H ≅ K) : IsLocal G K := sorry

section Coherent

variable [HasSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : C, ∀ V : Over U,
  HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{w}]
variable [∀ U : C, ∀ V : Over U,
  ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : C, ∀ V : Over U, ∀ W : Over V,
  HasWeakSheafify (((J.over U).over V).over W) AddCommGrpCat.{w}]
variable [∀ U : C, ∀ V : Over U, ∀ W : Over V,
  (((J.over U).over V).over W).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A module sheaf locally presented as a kernel between finite copies of a coherent sheaf is
coherent. -/
@[stacks 01CQ "coherence criterion"]
theorem IsLocal.isCoherent {G H : SheafOfModules.{w} R}
    (h : IsLocal G H) [G.IsCoherent] : H.IsCoherent := sorry

end Coherent

end SheafOfModules.RingedSite.FiniteKernel
