/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.Scheme.Module.RankOneReflexive
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sections of rank-one reflexive module sheaves

The section-power sequence attached to a section of a rank-one reflexive module sheaf, together
with its stalkwise isomorphism locus and pushforward-colimit comparison.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
variable [MonoidalCategory X.Modules] [BraidedCategory X.Modules] [MonoidalClosed X.Modules]

/-- The set of points `x` where a section `s : 𝟙_ X.Modules ⟶ ℱ` induces an isomorphism on
the stalk at `x`. -/
def rankOneReflexiveSectionIsoLocusSet {ℱ : X.Modules} (s : 𝟙_ X.Modules ⟶ ℱ) : Set X :=
  {x : X | IsIso (RingedSpace.moduleStalkHom x s)}

/-- The recursive reflexive powers of `ℱ`, starting with `𝟙_ X.Modules` and `ℱ`, with every
subsequent term the reflexive hull of `ℱ ⊗ rankOneReflexiveSectionPower ℱ (n + 1)`. -/
def rankOneReflexiveSectionPower (ℱ : X.Modules) : ℕ → X.Modules
  | 0 => 𝟙_ X.Modules
  | 1 => ℱ
  | n + 2 => reflexiveHull (ℱ ⊗ rankOneReflexiveSectionPower ℱ (n + 1))

/-- The transition maps in the reflexive-power sequence induced by a section
`s : 𝟙_ X.Modules ⟶ ℱ`. -/
noncomputable def rankOneReflexiveSectionPowerMap {ℱ : X.Modules}
    (s : 𝟙_ X.Modules ⟶ ℱ) :
    ∀ n : ℕ, rankOneReflexiveSectionPower ℱ n ⟶
      rankOneReflexiveSectionPower ℱ (n + 1)
  | 0 => s
  | n + 1 =>
      (λ_ (rankOneReflexiveSectionPower ℱ (n + 1))).inv ≫
        tensorHom s (𝟙 (rankOneReflexiveSectionPower ℱ (n + 1))) ≫
          toReflexiveHull (ℱ ⊗ rankOneReflexiveSectionPower ℱ (n + 1))

/-- The sequential diagram `𝟙_ X.Modules ⟶ ℱ ⟶ rankOneReflexiveSectionPower ℱ 2 ⟶ ⋯`
attached to a section of a module sheaf. -/
noncomputable def rankOneReflexiveSectionPowerDiagram {ℱ : X.Modules}
    (s : 𝟙_ X.Modules ⟶ ℱ) : ℕ ⥤ X.Modules :=
  Functor.ofSequence (rankOneReflexiveSectionPowerMap s)

/-- On an integral locally Noetherian normal scheme, the locus where a section of a coherent
rank-one reflexive `𝒪_X`-module induces an isomorphism on stalks is open. -/
@[stacks 0EBN]
theorem isOpen_rankOneReflexiveSectionIsoLocusSet
    (hXnormal : X.isNormal) (ℱ : X.Modules) [ℱ.IsCoherent] [IsRankOneReflexive X ℱ]
    (s : 𝟙_ X.Modules ⟶ ℱ) :
    IsOpen (rankOneReflexiveSectionIsoLocusSet s) := sorry

/-- If `U` is the open locus where a section `s` trivializes a coherent rank-one reflexive
`𝒪_X`-module `ℱ`, then the pushforward of `𝒪_U` is isomorphic to the colimit of the reflexive
section-power diagram of `s`. -/
@[stacks 0EBN]
theorem pushforward_tensorUnit_iso_colimit_rankOneReflexiveSectionPowerDiagram
    (hXnormal : X.isNormal) (ℱ : X.Modules) [ℱ.IsCoherent] [IsRankOneReflexive X ℱ]
    (s : 𝟙_ X.Modules ⟶ ℱ) (U : X.Opens)
    (hU : (U : Set X) = rankOneReflexiveSectionIsoLocusSet s) :
    Nonempty
      (((Scheme.Modules.pushforward U.ι).obj
          (SheafOfModules.unit (U : Scheme).ringCatSheaf : (U : Scheme).Modules)) ≅
        colimit (rankOneReflexiveSectionPowerDiagram s)) := sorry

end AlgebraicGeometry.Scheme.Modules
