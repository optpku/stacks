/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.LocalProperties
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Equivalence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Intrinsic local properties of module sheaves

The local module-theoretic predicates are preserved and reflected by inverse
image along a ringed equivalence.  The API is stated for `RingedSite` objects
themselves, so it does not depend on a chosen commutative-ring presentation.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules
open SheafOfModules.RingedSite

noncomputable section

universe uX vX uY vY w

namespace RingedSite.Hom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [∀ U : X, HasWeakSheafify (X.siteTopology.over U) AddCommGrpCat.{w}]
variable [∀ U : X,
  (X.siteTopology.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : Y, HasWeakSheafify (Y.siteTopology.over U) AddCommGrpCat.{w}]
variable [∀ U : Y,
  (Y.siteTopology.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (f : Hom X Y) [f.modulePushforward.{w}.IsRightAdjoint] [f.IsRingedEquivalence]

/-- Local freeness is preserved and reflected by a ringed equivalence. -/
@[stacks 03DM "(1)"]
theorem pullback_isLocallyFree_iff
    (M : SheafOfModules Y.structureSheaf) :
    (f.modulePullback.{w}.obj M).IsLocallyFree ↔ M.IsLocallyFree := sorry

/-- Finite local freeness is preserved and reflected by a ringed equivalence. -/
@[stacks 03DM "(2)"]
theorem pullback_isFiniteLocallyFree_iff
    (M : SheafOfModules Y.structureSheaf) :
    (f.modulePullback.{w}.obj M).IsFiniteLocallyFree ↔ M.IsFiniteLocallyFree := sorry

/-- Local generation by sections is preserved and reflected by a ringed equivalence. -/
@[stacks 03DM "(3)"]
theorem pullback_isLocallyGeneratedBySections_iff
    (M : SheafOfModules Y.structureSheaf) :
    IsLocallyGeneratedBySections (f.modulePullback.{w}.obj M) ↔
      IsLocallyGeneratedBySections M := sorry

/-- Local generation by a fixed number of sections is preserved and reflected by a ringed
equivalence. -/
@[stacks 03DM "(4)"]
theorem pullback_isLocallyGeneratedBy_iff
    (M : SheafOfModules Y.structureSheaf) (r : ℕ) :
    IsLocallyGeneratedBy (f.modulePullback.{w}.obj M) r ↔ IsLocallyGeneratedBy M r := sorry

/-- Finite type is preserved and reflected by a ringed equivalence. -/
@[stacks 03DM "(5)"]
theorem pullback_isFiniteType_iff
    (M : SheafOfModules Y.structureSheaf) :
    (f.modulePullback.{w}.obj M).IsFiniteType ↔ M.IsFiniteType := sorry

/-- Quasi-coherence is preserved and reflected by a ringed equivalence. -/
@[stacks 03DM "(6)"]
theorem pullback_isQuasicoherent_iff
    (M : SheafOfModules Y.structureSheaf) :
    (f.modulePullback.{w}.obj M).IsQuasicoherent ↔ M.IsQuasicoherent := sorry

/-- Finite presentation is preserved and reflected by a ringed equivalence. -/
@[stacks 03DM "(7)"]
theorem pullback_isFinitePresentation_iff
    (M : SheafOfModules Y.structureSheaf) :
    (f.modulePullback.{w}.obj M).IsFinitePresentation ↔ M.IsFinitePresentation := sorry

section Coherent

variable [∀ U : X, ∀ V : Over U,
  HasWeakSheafify ((X.siteTopology.over U).over V) AddCommGrpCat.{w}]
variable [∀ U : X, ∀ V : Over U,
  ((X.siteTopology.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : Y, ∀ V : Over U,
  HasWeakSheafify ((Y.siteTopology.over U).over V) AddCommGrpCat.{w}]
variable [∀ U : Y, ∀ V : Over U,
  ((Y.siteTopology.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Coherence is preserved and reflected by a ringed equivalence. -/
@[stacks 03DM "(8)"]
theorem pullback_isCoherent_iff
    (M : SheafOfModules Y.structureSheaf) :
    IsCoherent (f.modulePullback.{w}.obj M) ↔ IsCoherent M := sorry

end Coherent

end RingedSite.Hom
