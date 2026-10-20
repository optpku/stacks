/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.RankOneReflexive.Section.AffineCriterion
import StacksCheckRecall

/-!
# Lemma 31.29.6

An affine criterion for the isomorphism locus of a rank-one reflexive section.

@stack 0EBR
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

universe u

/- Lemma 31.29.6: For an integral locally Noetherian normal scheme, a coherent rank-one
reflexive module, a section, and its isomorphism-locus open `U`, the inclusion `U.ι` is affine
if and only if every point outside `U` has a positive section power in the maximal ideal times
the corresponding reflexive-power stalk. -/
@[stacks 0EBR]
#check
  (AlgebraicGeometry.Scheme.Modules.RankOneReflexiveSection.isAffineHom_iff :
    ∀ {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X],
      X.isNormal →
        ∀ (ℱ : X.Modules) [ℱ.IsCoherent] [Scheme.Modules.IsRankOneReflexive X ℱ]
          (s : 𝟙_ X.Modules ⟶ ℱ) (U : X.Opens),
          (U : Set X) = Scheme.Modules.rankOneReflexiveSectionIsoLocusSet s →
            (IsAffineHom U.ι ↔
              ∀ x : X, x ∉ (U : Set X) →
                ∃ n : ℕ, 0 < n ∧
                  Scheme.Modules.rankOneReflexiveSectionPowerStalkElement s n x ∈
                    IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
                      (⊤ : Submodule (X.presheaf.stalk x)
                        ((TopCat.Presheaf.stalk
                          (Scheme.Modules.rankOneReflexiveSectionPower ℱ n).val.presheaf x :
                            AddCommGrpCat) : Type u))))
