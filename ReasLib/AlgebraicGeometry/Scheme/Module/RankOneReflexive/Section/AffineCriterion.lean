/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.RankOneReflexive.Section.StalkPower
import Mathlib.Tactic.CrossRefAttribute

/-!
# Affine criterion for a rank-one reflexive section

This file gives a criterion detecting when the isomorphism locus of a section has affine
inclusion.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

namespace RankOneReflexiveSection

/-- For a coherent rank-one reflexive module on an integral locally Noetherian normal scheme,
the inclusion of the isomorphism locus of a section is affine if and only if every point outside
the locus has a positive section power lying in the maximal ideal times the corresponding
reflexive-power stalk. -/
@[stacks 0EBR]
theorem isAffineHom_iff
    (hXnormal : X.isNormal) (ℱ : X.Modules) [ℱ.IsCoherent] [IsRankOneReflexive X ℱ]
    (s : 𝟙_ X.Modules ⟶ ℱ) (U : X.Opens)
    (hU : (U : Set X) = rankOneReflexiveSectionIsoLocusSet s) :
    IsAffineHom U.ι ↔
      ∀ x : X, x ∉ (U : Set X) →
        ∃ n : ℕ, 0 < n ∧
          rankOneReflexiveSectionPowerStalkElement s n x ∈
            IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
              (⊤ : Submodule (X.presheaf.stalk x)
                ((TopCat.Presheaf.stalk
                  (rankOneReflexiveSectionPower ℱ n).val.presheaf x :
                    AddCommGrpCat) : Type u)) := sorry

end RankOneReflexiveSection

end AlgebraicGeometry.Scheme.Modules
