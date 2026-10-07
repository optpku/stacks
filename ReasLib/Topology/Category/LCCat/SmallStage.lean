module

public import ReasLib.Topology.Category.LCCat.Sites
public import Mathlib.CategoryTheory.Countable
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

/-- A cardinal bound has the closure points required by the set-theoretic replacement step in
Remark 21.31.5.  In a foundational development this condition is supplied by the chosen
replacement theorem for the universe of sets. -/
def IsReplacementBound (Bound : Cardinal.{u} → Cardinal.{u}) : Prop :=
  ∀ κ : Cardinal.{u}, ∃ κ' : Cardinal.{u},
    κ ≤ κ' ∧ Order.succ Cardinal.aleph0.{u} ≤ κ' ∧
      ∀ ⦃μ : Cardinal.{u}⦄, μ ≤ κ' → Bound μ ≤ κ'

/-- A stage is closed under every countable diagram shape represented in the stage universe. -/
class IsClosedUnderCountableLimits (P : ObjectProperty LCCat.{u}) : Prop where
  isClosedUnderLimitsOfShape {J : Type u} [SmallCategory J] [CountableCategory J] :
    P.IsClosedUnderLimitsOfShape J

/-- A stage is closed under every countable colimit shape represented in the stage universe. -/
class IsClosedUnderCountableColimits (P : ObjectProperty LCCat.{u}) : Prop where
  isClosedUnderColimitsOfShape {J : Type u} [SmallCategory J] [CountableCategory J] :
    P.IsClosedUnderColimitsOfShape J

/-- Typeclass access to the limit closure of any represented countable shape. -/
instance instIsClosedUnderCountableLimitShape
    (P : ObjectProperty LCCat.{u}) [IsClosedUnderCountableLimits P]
    {J : Type u} [SmallCategory J] [CountableCategory J] :
    P.IsClosedUnderLimitsOfShape J := sorry

/-- Typeclass access to the colimit closure of any represented countable shape. -/
instance instIsClosedUnderCountableColimitShape
    (P : ObjectProperty LCCat.{u}) [IsClosedUnderCountableColimits P]
    {J : Type u} [SmallCategory J] [CountableCategory J] :
    P.IsClosedUnderColimitsOfShape J := sorry

/-- The bounded-size replacement clause for a stage property.  The conclusion uses the canonical
`isoClosure` owner, so downstream arguments need not unpack a witness object or an isomorphism. -/
def IsClosedUnderBoundedSize
    (P : ObjectProperty LCCat.{u}) (Bound : Cardinal.{u} → Cardinal.{u}) : Prop :=
  ∀ ⦃X Y : LCCat.{u}⦄, P X →
    Cardinal.mk Y.obj ≤ Bound (Cardinal.mk X.obj) → P.isoClosure Y

/-- Countable-limit closure gives the pullback closure needed by the qc pretopology.  The proof
also transports the countable shape from its canonical small representative to `WalkingCospan`. -/
@[stacks 09X2 "countable limits imply pullback closure"]
instance instIsClosedUnderPullbacks
    (P : ObjectProperty LCCat.{u}) [IsClosedUnderCountableLimits P] :
    P.IsClosedUnderLimitsOfShape WalkingCospan := sorry

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
    (toAmbient 𝒰).toPresieve = 𝒰.toPresieve.map P.ι := sorry

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
    R ∈ qcPrecoverage P U ↔ R.map P.ι ∈ LCCat.qcPrecoverage U.obj := sorry

/-- An internal family is qc-covering precisely when its ambient presentation is qc-covering. -/
@[stacks 09X2 "qc family criterion on a small stage"]
theorem isCovering_qcPrecoverage_iff
    {P : ObjectProperty LCCat.{u}} {U : P.FullSubcategory}
    (𝒰 : SemiRepresentableFamily.Over.{w} U) :
    𝒰.IsCovering (qcPrecoverage P) ↔
      (toAmbient 𝒰).IsQuasiCompactCovering := sorry

/-- The stage qc precoverage contains singleton isomorphism families. -/
instance instQcPrecoverageHasIsos
    (P : ObjectProperty LCCat.{u}) : (qcPrecoverage P).HasIsos := sorry

/-- The stage qc precoverage is stable under composition. -/
instance instQcPrecoverageIsStableUnderComposition
    (P : ObjectProperty LCCat.{u}) :
    (qcPrecoverage P).IsStableUnderComposition := sorry

/-- The qc precoverage on a pullback-closed stage has the base-change axiom. -/
instance instQcPrecoverageIsStableUnderBaseChange
    (P : ObjectProperty LCCat.{u}) [P.IsClosedUnderLimitsOfShape WalkingCospan] :
    (qcPrecoverage P).IsStableUnderBaseChange := sorry

/-- The qc pretopology on a pullback-closed stage is obtained from the canonical qc precoverage. -/
@[stacks 09X2 "qc pretopology on a small full subcategory"]
def qcPretopology (P : ObjectProperty LCCat.{u})
    [P.IsClosedUnderLimitsOfShape WalkingCospan] :
    Pretopology P.FullSubcategory :=
  (qcPrecoverage P).toPretopology

/-- The Grothendieck topology generated by the canonical qc pretopology on a stage. -/
@[stacks 09X2 "qc topology on a small full subcategory"]
def qcTopology (P : ObjectProperty LCCat.{u})
    [P.IsClosedUnderLimitsOfShape WalkingCospan] :
    GrothendieckTopology P.FullSubcategory :=
  (qcPretopology P).toGrothendieck

@[simp]
theorem isCovering_qcPretopology_iff
    {P : ObjectProperty LCCat.{u}}
    [P.IsClosedUnderLimitsOfShape WalkingCospan]
    {U : P.FullSubcategory} {𝒰 : SemiRepresentableFamily.Over.{w} U} :
    𝒰.IsCovering (qcPretopology P).toPrecoverage ↔
      𝒰.IsCovering (qcPrecoverage P) := sorry

/-! ### The source-facing stage owner -/

end LCCat.SmallStage

namespace LCCat

/-- A small stage packages its concrete object property together with the closure and replacement
conditions used in Remark 21.31.5.  Its canonical qc site is
`SmallStage.qcTopology property`; no representative-covering set is hidden in this owner. -/
@[stacks 09X2 "small stage owner"]
structure SmallStage (Bound : Cardinal.{u} → Cardinal.{u}) where
  /-- The objects retained by the stage. -/
  property : ObjectProperty LCCat.{u}
  /-- The stage is small in the selected universe. -/
  small : ObjectProperty.Small.{w} property
  /-- Closure under countable limits. -/
  limits : SmallStage.IsClosedUnderCountableLimits property
  /-- Closure under countable colimits. -/
  colimits : SmallStage.IsClosedUnderCountableColimits property
  /-- Closure under the source's cardinal replacement bound. -/
  boundedSize : SmallStage.IsClosedUnderBoundedSize property Bound

end LCCat

namespace LCCat.SmallStage

/-- Smallness is available to typeclass search for every bundled stage. -/
instance instSmall {Bound : Cardinal.{u} → Cardinal.{u}}
    (S : LCCat.SmallStage.{u, w} Bound) :
    ObjectProperty.Small.{w} S.property := sorry

/-- Countable-limit closure is available to typeclass search for every bundled stage. -/
instance instCountableLimits {Bound : Cardinal.{u} → Cardinal.{u}}
    (S : LCCat.SmallStage.{u, w} Bound) :
    IsClosedUnderCountableLimits S.property := sorry

/-- Countable-colimit closure is available to typeclass search for every bundled stage. -/
instance instCountableColimits {Bound : Cardinal.{u} → Cardinal.{u}}
    (S : LCCat.SmallStage.{u, w} Bound) :
    IsClosedUnderCountableColimits S.property := sorry

/-- The canonical qc precoverage associated with a bundled small stage. -/
abbrev qcPrecoverageOf {Bound : Cardinal.{u} → Cardinal.{u}}
    (S : SmallStage.{u, w} Bound) :
    Precoverage S.property.FullSubcategory :=
  qcPrecoverage S.property

/-- The canonical qc pretopology associated with a bundled small stage. -/
abbrev qcPretopologyOf {Bound : Cardinal.{u} → Cardinal.{u}}
    (S : SmallStage.{u, w} Bound) :
    Pretopology S.property.FullSubcategory :=
  qcPretopology S.property

/-- The canonical qc topology associated with a bundled small stage. -/
abbrev qcTopologyOf {Bound : Cardinal.{u} → Cardinal.{u}}
    (S : SmallStage.{u, w} Bound) :
    GrothendieckTopology S.property.FullSubcategory :=
  qcTopology S.property

/-! ### The set-theoretic existence statement -/

/-- Remark 21.31.5 (09X2): for a set-sized initial family `S₀` in `LCCat`, set-theoretic
replacement supplies a small stage containing it, closed under all countable limits and colimits
which exist in `LCCat`, and satisfying the chosen bounded-size clause.  The associated qc site is
the canonical `qcTopology` above; the textbook's representative set `Cov` is therefore represented
by this concrete precoverage rather than by an existential package. -/
@[stacks 09X2]
theorem exists_containing
    {I : Type w} (Bound : Cardinal.{u} → Cardinal.{u})
    (hBound : IsReplacementBound Bound) (S₀ : I → LCCat.{u}) :
    ∃ S : SmallStage.{u, w} Bound, ∀ i, S.property (S₀ i) := sorry

end LCCat.SmallStage

end
