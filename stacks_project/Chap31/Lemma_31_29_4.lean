/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.RankOneReflexive.Section.Codimension
import StacksCheckRecall

/-!
# Lemma 31.29.4

Codimension of the complement of the isomorphism locus of a nonzero section.

@stack 0EBP
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe u

/- Lemma 31.29.4: If a section of a coherent rank-one reflexive module on an integral locally
Noetherian normal scheme is nonzero, then every irreducible component of the complement of its
isomorphism locus has codimension one. -/
@[stacks 0EBP] #check
  (AlgebraicGeometry.Scheme.Modules.RankOneReflexiveSection.component_coheight_eq_one :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
      [AlgebraicGeometry.IsLocallyNoetherian X]
      [CategoryTheory.MonoidalCategory X.Modules] [CategoryTheory.BraidedCategory X.Modules]
      [CategoryTheory.MonoidalClosed X.Modules],
      X.isNormal → ∀ (ℱ : X.Modules) [ℱ.IsCoherent]
        [AlgebraicGeometry.Scheme.Modules.IsRankOneReflexive X ℱ]
        (s : 𝟙_ X.Modules ⟶ ℱ),
        s ≠ 0 → ∀ (U : X.Opens),
          (U : Set X) =
            AlgebraicGeometry.Scheme.Modules.rankOneReflexiveSectionIsoLocusSet s →
          ∀ Z : TopologicalSpace.IrreducibleCloseds X,
            Maximal
              (fun Y : TopologicalSpace.IrreducibleCloseds X ↦
                (Y : Set X) ⊆ ((U : Set X)ᶜ : Set X)) Z →
              Order.coheight Z = 1)
