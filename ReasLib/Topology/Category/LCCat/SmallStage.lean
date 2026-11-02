/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Category.LCCat.Sites
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Countable
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.ObjectProperty.LimitsClosure
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsCardinalClosure
public import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.Tactic.CrossRefAttribute

/-!
# Small stages for the `LCCat` sites

The category of Hausdorff locally compact spaces is large.  This module owns the reusable
small-stage interface used when a site argument needs a set-sized full subcategory.  The site on a
stage is not an existentially chosen package: it is the canonical pullback of the ambient qc
precoverage along the full-subcategory inclusion.
-/

@[expose] public section

universe u w v

open CategoryTheory CategoryTheory.Limits

namespace LCCat.SmallStage

/-! ### Size and closure predicates -/

/-- A property of objects of `LCCat` is closed under countable limits up to isomorphism: whenever
a countable diagram of objects satisfying `P` has a limit in `LCCat`, that limit is isomorphic to
an object satisfying `P`.  Equivalently, the isomorphism closure of `P` is closed under limits of
every countable shape `J : Type u`.  The closure is only up to isomorphism because a set-sized
stage keeps one representative per object, never a whole isomorphism class. -/
class IsClosedUnderCountableLimits (P : ObjectProperty LCCat.{u}) : Prop where
  isoClosure_isClosedUnderLimitsOfShape {J : Type u} [SmallCategory J] [CountableCategory J] :
    P.isoClosure.IsClosedUnderLimitsOfShape J

/-- A property of objects of `LCCat` is closed under countable colimits up to isomorphism: the
isomorphism closure of `P` is closed under colimits of every countable shape `J : Type u`. -/
class IsClosedUnderCountableColimits (P : ObjectProperty LCCat.{u}) : Prop where
  isoClosure_isClosedUnderColimitsOfShape {J : Type u} [SmallCategory J] [CountableCategory J] :
    P.isoClosure.IsClosedUnderColimitsOfShape J

/-- Typeclass access to the closure of `P.isoClosure` under limits of a countable shape. -/
instance instIsClosedUnderCountableLimitShape
    (P : ObjectProperty LCCat.{u}) [IsClosedUnderCountableLimits P]
    {J : Type u} [SmallCategory J] [CountableCategory J] :
    P.isoClosure.IsClosedUnderLimitsOfShape J :=
  IsClosedUnderCountableLimits.isoClosure_isClosedUnderLimitsOfShape

/-- Typeclass access to the closure of `P.isoClosure` under colimits of a countable shape. -/
instance instIsClosedUnderCountableColimitShape
    (P : ObjectProperty LCCat.{u}) [IsClosedUnderCountableColimits P]
    {J : Type u} [SmallCategory J] [CountableCategory J] :
    P.isoClosure.IsClosedUnderColimitsOfShape J :=
  IsClosedUnderCountableColimits.isoClosure_isClosedUnderColimitsOfShape

/-- A limit in `LCCat` of a countable diagram in `P` is isomorphic to an object of `P`. -/
theorem limitsOfShape_le_isoClosure
    (P : ObjectProperty LCCat.{u}) [IsClosedUnderCountableLimits P]
    (J : Type u) [SmallCategory J] [CountableCategory J] :
    P.limitsOfShape J ≤ P.isoClosure := by
  rw [← ObjectProperty.limitsOfShape_isoClosure]
  exact ObjectProperty.IsClosedUnderLimitsOfShape.limitsOfShape_le P.isoClosure J

/-- A colimit in `LCCat` of a countable diagram in `P` is isomorphic to an object of `P`. -/
theorem colimitsOfShape_le_isoClosure
    (P : ObjectProperty LCCat.{u}) [IsClosedUnderCountableColimits P]
    (J : Type u) [SmallCategory J] [CountableCategory J] :
    P.colimitsOfShape J ≤ P.isoClosure := by
  rw [← ObjectProperty.colimitsOfShape_isoClosure]
  exact ObjectProperty.IsClosedUnderColimitsOfShape.colimitsOfShape_le P.isoClosure J

/-- The bounded-size clause for a property of objects: if `P X` and the underlying set of `Y`
has cardinality at most `Bound (size X)`, then `Y` is isomorphic to an object satisfying `P`. -/
def IsClosedUnderBoundedSize
    (P : ObjectProperty LCCat.{u}) (Bound : Cardinal.{u} → Cardinal.{u}) : Prop :=
  ∀ ⦃X Y : LCCat.{u}⦄, P X →
    Cardinal.mk Y.obj ≤ Bound (Cardinal.mk X.obj) → P.isoClosure Y

/-- Closure under countable limits up to isomorphism implies that `P.isoClosure` is closed under
pullbacks: `WalkingCospan` is finite, and is equivalent to its countable representative in
`Type u`. -/
@[stacks 09X2 "countable limits imply pullback closure"]
instance instIsClosedUnderPullbacks
    (P : ObjectProperty LCCat.{u}) [IsClosedUnderCountableLimits P] :
    P.isoClosure.IsClosedUnderLimitsOfShape WalkingCospan := by
  exact ObjectProperty.IsClosedUnderLimitsOfShape.of_equivalence
    (ULiftHomULiftCategory.equiv.{u, u} WalkingCospan).symm

/-- A full subcategory of `LCCat` whose isomorphism closure is closed under pullbacks has
pullbacks: it is equivalent to the full subcategory on its isomorphism closure. -/
instance instHasPullbacks
    (P : ObjectProperty LCCat.{u}) [P.isoClosure.IsClosedUnderLimitsOfShape WalkingCospan] :
    HasPullbacks P.FullSubcategory :=
  Adjunction.hasLimitsOfShape_of_equivalence (ObjectProperty.ιOfLE P.le_isoClosure)

/-! ### The canonical qc site on a full subcategory -/

/-- The ambient fixed-target family underlying an internal family on a full subcategory. -/
def toAmbient
    {P : ObjectProperty LCCat.{u}} {U : P.FullSubcategory}
    (𝒰 : SemiRepresentableFamily.Over.{w} U) :
    SemiRepresentableFamily.Over.{w} U.obj :=
  SemiRepresentableFamily.Over.ofArrows
    (fun i ↦ ((𝒰.obj i).left).obj)
    (fun i ↦ P.ι.map (𝒰.obj i).hom)

/-- The generated presieve of `toAmbient` is the image of the internal generated presieve under
the full-subcategory inclusion. -/
@[simp]
theorem toAmbient_toPresieve
    {P : ObjectProperty LCCat.{u}} {U : P.FullSubcategory}
    (𝒰 : SemiRepresentableFamily.Over.{w} U) :
    (toAmbient 𝒰).toPresieve = 𝒰.toPresieve.map P.ι := by
  exact (Presieve.map_ofArrows (F := P.ι) (fun i ↦ (𝒰.obj i).hom)).symm

/-- The qc precoverage on `P.FullSubcategory` is the canonical comap of the ambient qc
precoverage.  In particular, a covering presieve retains its concrete ambient presentation. -/
@[stacks 09X2 "qc precoverage on a small full subcategory"]
def qcPrecoverage (P : ObjectProperty LCCat.{u}) :
    Precoverage P.FullSubcategory :=
  LCCat.qcPrecoverage.comap P.ι

/-- Membership in the stage qc precoverage is exactly membership of the mapped presieve in the
ambient qc precoverage. -/
@[simp]
theorem mem_qcPrecoverage_iff
    {P : ObjectProperty LCCat.{u}} {U : P.FullSubcategory} {R : Presieve U} :
    R ∈ qcPrecoverage P U ↔ R.map P.ι ∈ LCCat.qcPrecoverage U.obj := by
  rfl

/-- An internal family is qc-covering precisely when its ambient presentation is qc-covering. -/
@[stacks 09X2 "qc family criterion on a small stage"]
theorem isCovering_qcPrecoverage_iff
    {P : ObjectProperty LCCat.{u}} {U : P.FullSubcategory}
    (𝒰 : SemiRepresentableFamily.Over.{w} U) :
    𝒰.IsCovering (qcPrecoverage P) ↔
      (toAmbient 𝒰).IsQuasiCompactCovering := by
  rw [← LCCat.isCovering_qcPrecoverage_iff]
  change 𝒰.toPresieve ∈ qcPrecoverage P U ↔
    (toAmbient 𝒰).toPresieve ∈ LCCat.qcPrecoverage U.obj
  rw [toAmbient_toPresieve]
  exact mem_qcPrecoverage_iff

/-- The stage qc precoverage contains singleton isomorphism families. -/
instance instQcPrecoverageHasIsos
    (P : ObjectProperty LCCat.{u}) : (qcPrecoverage P).HasIsos := by
  unfold qcPrecoverage
  infer_instance

/-- The stage qc precoverage is stable under composition. -/
instance instQcPrecoverageIsStableUnderComposition
    (P : ObjectProperty LCCat.{u}) :
    (qcPrecoverage P).IsStableUnderComposition := by
  unfold qcPrecoverage
  infer_instance

/-- The qc precoverage on a pullback-closed stage has the base-change axiom. -/
instance instQcPrecoverageIsStableUnderBaseChange
    (P : ObjectProperty LCCat.{u}) [P.isoClosure.IsClosedUnderLimitsOfShape WalkingCospan] :
    (qcPrecoverage P).IsStableUnderBaseChange := by
  letI : PreservesLimitsOfShape WalkingCospan P.ι :=
    preservesLimitsOfShape_of_natIso (ObjectProperty.ιOfLECompιIso P.le_isoClosure)
  unfold qcPrecoverage
  infer_instance

/-- The qc pretopology on a pullback-closed stage is obtained from the canonical qc precoverage. -/
@[stacks 09X2 "qc pretopology on a small full subcategory"]
def qcPretopology (P : ObjectProperty LCCat.{u})
    [P.isoClosure.IsClosedUnderLimitsOfShape WalkingCospan] :
    Pretopology P.FullSubcategory :=
  (qcPrecoverage P).toPretopology

/-- The Grothendieck topology generated by the canonical qc pretopology on a stage. -/
@[stacks 09X2 "qc topology on a small full subcategory"]
def qcTopology (P : ObjectProperty LCCat.{u})
    [P.isoClosure.IsClosedUnderLimitsOfShape WalkingCospan] :
    GrothendieckTopology P.FullSubcategory :=
  (qcPretopology P).toGrothendieck

@[simp]
theorem isCovering_qcPretopology_iff
    {P : ObjectProperty LCCat.{u}}
    [P.isoClosure.IsClosedUnderLimitsOfShape WalkingCospan]
    {U : P.FullSubcategory} {𝒰 : SemiRepresentableFamily.Over.{w} U} :
    𝒰.IsCovering (qcPretopology P).toPrecoverage ↔
      𝒰.IsCovering (qcPrecoverage P) := by
  rfl

/-! ### The source-facing stage owner -/

end LCCat.SmallStage

namespace LCCat

/-- A small stage of `LCCat` for a cardinal function `Bound`: a set (a `u`-small family) of
representative objects whose countable limits and colimits existing in `LCCat` are isomorphic to
members, and which contains, up to isomorphism, every space of size at most `Bound (size X)` for
each member `X`.  The property itself is not closed under isomorphisms.  Its canonical qc site is
`SmallStage.qcTopology property`; no representative-covering set is hidden in this owner. -/
@[stacks 09X2 "small stage owner"]
structure SmallStage (Bound : Cardinal.{u} → Cardinal.{u}) where
  /-- The representative objects retained by the stage. -/
  property : ObjectProperty LCCat.{u}
  /-- The representatives form a set: the stage is `u`-small. -/
  small : ObjectProperty.Small.{u} property
  /-- Countable limits existing in `LCCat` are isomorphic to objects of the stage. -/
  limits : SmallStage.IsClosedUnderCountableLimits property
  /-- Countable colimits existing in `LCCat` are isomorphic to objects of the stage. -/
  colimits : SmallStage.IsClosedUnderCountableColimits property
  /-- Spaces of size at most `Bound (size X)`, for `X` in the stage, are isomorphic to objects of
  the stage. -/
  boundedSize : SmallStage.IsClosedUnderBoundedSize property Bound

end LCCat

namespace LCCat.SmallStage

/-- Smallness is available to typeclass search for every bundled stage. -/
instance instSmall {Bound : Cardinal.{u} → Cardinal.{u}}
    (S : LCCat.SmallStage.{u} Bound) :
    ObjectProperty.Small.{u} S.property :=
  S.small

/-- Countable-limit closure is available to typeclass search for every bundled stage. -/
instance instCountableLimits {Bound : Cardinal.{u} → Cardinal.{u}}
    (S : LCCat.SmallStage.{u} Bound) :
    IsClosedUnderCountableLimits S.property :=
  S.limits

/-- Countable-colimit closure is available to typeclass search for every bundled stage. -/
instance instCountableColimits {Bound : Cardinal.{u} → Cardinal.{u}}
    (S : LCCat.SmallStage.{u} Bound) :
    IsClosedUnderCountableColimits S.property :=
  S.colimits

/-- The canonical qc precoverage associated with a bundled small stage. -/
abbrev qcPrecoverageOf {Bound : Cardinal.{u} → Cardinal.{u}}
    (S : SmallStage.{u} Bound) :
    Precoverage S.property.FullSubcategory :=
  qcPrecoverage S.property

/-- The canonical qc pretopology associated with a bundled small stage. -/
abbrev qcPretopologyOf {Bound : Cardinal.{u} → Cardinal.{u}}
    (S : SmallStage.{u} Bound) :
    Pretopology S.property.FullSubcategory :=
  qcPretopology S.property

/-- The canonical qc topology associated with a bundled small stage. -/
abbrev qcTopologyOf {Bound : Cardinal.{u} → Cardinal.{u}}
    (S : SmallStage.{u} Bound) :
    GrothendieckTopology S.property.FullSubcategory :=
  qcTopology S.property

/-! ### The set-theoretic existence statement -/

/-- For every cardinal function `Bound` and every set-indexed family `S₀` of objects of `LCCat`,
there is a small stage for `Bound` containing every `S₀ i`.  The associated qc site is the
canonical `qcTopology` above; a representative set of coverings is therefore given by this
concrete precoverage rather than by an existential package. -/
@[stacks 09X2]
theorem exists_containing
    {I : Type u} (Bound : Cardinal.{u} → Cardinal.{u}) (S₀ : I → LCCat.{u}) :
    ∃ S : SmallStage.{u} Bound, ∀ i, S.property (S₀ i) := sorry

end LCCat.SmallStage

end
