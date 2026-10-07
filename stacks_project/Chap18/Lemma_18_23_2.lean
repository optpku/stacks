module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Intrinsic
import StacksCheckRecall

/-!
# Lemma 18.23.2

The reusable owner is
`ReasLib.AlgebraicGeometry.RingedSite.Module.Intrinsic`.  This chapter entry only recalls its
eight atomic preservation-and-reflection statements.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules
open SheafOfModules.RingedSite

universe uX vX uY vY w

namespace RingedSite.Hom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [∀ U : X, HasWeakSheafify (X.siteTopology.over U) AddCommGrpCat.{w}]
variable [∀ U : X,
  (X.siteTopology.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : Y, HasWeakSheafify (Y.siteTopology.over U) AddCommGrpCat.{w}]
variable [∀ U : Y,
  (Y.siteTopology.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (f : Hom X Y) [f.modulePushforward.{w}.IsRightAdjoint]
  [f.IsRingedEquivalence] (M : ModuleCat.{w} Y)

/- Lemma 18.23.2 (1) (03DM): local freeness is intrinsic. -/
@[stacks 03DM "(1)"]
#check (pullback_isLocallyFree_iff f M :
  (f.modulePullback.{w}.obj M).IsLocallyFree ↔ M.IsLocallyFree)

/- Lemma 18.23.2 (2) (03DM): finite local freeness is intrinsic. -/
@[stacks 03DM "(2)"]
#check (pullback_isFiniteLocallyFree_iff f M :
  (f.modulePullback.{w}.obj M).IsFiniteLocallyFree ↔ M.IsFiniteLocallyFree)

/- Lemma 18.23.2 (3) (03DM): local generation by sections is intrinsic. -/
@[stacks 03DM "(3)"]
#check (pullback_isLocallyGeneratedBySections_iff f M :
  IsLocallyGeneratedBySections (f.modulePullback.{w}.obj M) ↔
    IsLocallyGeneratedBySections M)

/- Lemma 18.23.2 (4) (03DM): local generation by `r` sections is intrinsic. -/
@[stacks 03DM "(4)"]
#check (pullback_isLocallyGeneratedBy_iff f M : ∀ r,
  IsLocallyGeneratedBy (f.modulePullback.{w}.obj M) r ↔ IsLocallyGeneratedBy M r)

/- Lemma 18.23.2 (5) (03DM): finite type is intrinsic. -/
@[stacks 03DM "(5)"]
#check (pullback_isFiniteType_iff f M :
  (f.modulePullback.{w}.obj M).IsFiniteType ↔ M.IsFiniteType)

/- Lemma 18.23.2 (6) (03DM): quasi-coherence is intrinsic. -/
@[stacks 03DM "(6)"]
#check (pullback_isQuasicoherent_iff f M :
  (f.modulePullback.{w}.obj M).IsQuasicoherent ↔ M.IsQuasicoherent)

/- Lemma 18.23.2 (7) (03DM): finite presentation is intrinsic. -/
@[stacks 03DM "(7)"]
#check (pullback_isFinitePresentation_iff f M :
  (f.modulePullback.{w}.obj M).IsFinitePresentation ↔ M.IsFinitePresentation)

section Coherent

variable [∀ U : X, ∀ V : Over U,
  HasWeakSheafify ((X.siteTopology.over U).over V) AddCommGrpCat.{w}]
variable [∀ U : X, ∀ V : Over U,
  ((X.siteTopology.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : Y, ∀ V : Over U,
  HasWeakSheafify ((Y.siteTopology.over U).over V) AddCommGrpCat.{w}]
variable [∀ U : Y, ∀ V : Over U,
  ((Y.siteTopology.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/- Lemma 18.23.2 (8) (03DM): coherence is intrinsic. -/
@[stacks 03DM "(8)"]
#check (pullback_isCoherent_iff f M :
  IsCoherent (f.modulePullback.{w}.obj M) ↔ IsCoherent M)

end Coherent

end RingedSite.Hom
