/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.RankOneReflexive.Section
import Mathlib.Tactic.CrossRefAttribute

/-!
# Codimension of the isomorphism locus complement of a rank-one reflexive section

Irreducible components of the complement of the isomorphism locus of a nonzero section of a
rank-one reflexive module on a normal scheme have codimension one.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
variable [MonoidalCategory X.Modules] [BraidedCategory X.Modules] [MonoidalClosed X.Modules]

namespace RankOneReflexiveSection

/-- Every irreducible component of the complement of the isomorphism locus of a nonzero section
of a coherent rank-one reflexive module on an integral locally Noetherian normal scheme has
codimension one. Components are represented by maximal irreducible closed subsets contained in
the complement of the locus, and codimension is measured by `Order.coheight`. -/
@[stacks 0EBP]
theorem component_coheight_eq_one
    (hXnormal : X.isNormal) (ℱ : X.Modules) [ℱ.IsCoherent] [IsRankOneReflexive X ℱ]
    (s : 𝟙_ X.Modules ⟶ ℱ) (hs : s ≠ 0) (U : X.Opens)
    (hU : (U : Set X) = rankOneReflexiveSectionIsoLocusSet s) :
    ∀ Z : IrreducibleCloseds X,
      Maximal (fun Y : IrreducibleCloseds X ↦ (Y : Set X) ⊆ ((U : Set X)ᶜ : Set X)) Z →
        Order.coheight Z = 1 := sorry

end RankOneReflexiveSection

end AlgebraicGeometry.Scheme.Modules
