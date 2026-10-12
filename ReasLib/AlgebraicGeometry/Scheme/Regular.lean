/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReasLib.AlgebraicGeometry.Scheme.LocalRingProperty.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Regular schemes

A scheme is regular if its points admit affine open neighborhoods whose rings of sections are
regular. This file also records the corresponding affine-open criterion, local Noetherianity, and
regularity of local rings.
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- A scheme is regular if every point admits an affine open neighborhood whose coordinate ring
satisfies `IsRegularRing`, which includes Noetherianity. -/
@[stacks 02IS]
abbrev Regular (X : Scheme.{u}) : Prop :=
  X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsRegularRing A)

/-- On a regular scheme, every point lies in an affine open neighborhood with regular coordinate
ring. -/
theorem exists_affineOpen_regularRing (X : Scheme.{u}) [Regular X] (x : X) :
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ IsRegularRing (Γ(X, (U : X.Opens))) := by
  exact HasRingPropertyLocally.exists_affineOpen X (fun A : CommRingCat.{u} ↦ IsRegularRing A) x

/-- Unfold `Regular` into the affine-open neighborhood condition on points. -/
theorem regular_iff (X : Scheme.{u}) :
    Regular X ↔
      ∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ IsRegularRing (Γ(X, (U : X.Opens))) := by
  exact hasRingPropertyLocally_iff X (fun A : CommRingCat.{u} ↦ IsRegularRing A)

/-- A regular scheme is locally Noetherian. -/
noncomputable instance instIsLocallyNoetherianOfRegular [Regular X] : IsLocallyNoetherian X := by
  let hX : X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsRegularRing A) :=
    inferInstance
  let U : X → X.affineOpens := fun x ↦ Classical.choose (hX.out x)
  have hU_mem : ∀ x : X, x ∈ ((U x : X.affineOpens) : X.Opens) := fun x ↦
    (Classical.choose_spec (hX.out x)).1
  have hU_regular : ∀ x : X, IsRegularRing (Γ(X, ((U x : X.affineOpens) : X.Opens))) :=
    fun x ↦ (Classical.choose_spec (hX.out x)).2
  have hU_cover : ⨆ x, ((U x : X.affineOpens) : X.Opens) = ⊤ := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨x, hU_mem x⟩
  have hU_noetherian :
      ∀ x, IsNoetherianRing ↑Γ(X, ((U x : X.affineOpens) : X.Opens)) := by
    intro x
    exact (hU_regular x).toIsNoetherian
  exact AlgebraicGeometry.isLocallyNoetherian_of_affine_cover hU_cover hU_noetherian

/-- The stalk of a regular scheme at any point is a regular local ring. -/
theorem isRegularLocalRing_stalk (X : Scheme.{u}) [Regular X] (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨U, hxU, hU⟩ := exists_affineOpen_regularRing X x
  -- Local instance justification (proof-local temporary data): Regular-ring localization uses the chosen affine section-ring hypothesis through typeclass inference.
  letI : IsRegularRing Γ(X, (U : X.Opens)) := hU
  -- Local instance justification (proof-local temporary data): The section-to-stalk algebra structure is required by the localization equivalence at the chosen point.
  letI : Algebra Γ(X, (U : X.Opens)) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  let p := U.2.primeIdealOf ⟨x, hxU⟩
  -- Local instance justification (proof-local temporary data): The stalk-localization API needs the chosen affine-open stalk as a localization at the point prime.
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    U.2.isLocalization_stalk ⟨x, hxU⟩
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal) (X.presheaf.stalk x)).toRingEquiv

/-- A scheme is regular exactly when it is locally Noetherian and all its stalks are regular local
rings. -/
theorem regular_iff_isLocallyNoetherian_and_forall_isRegularLocalRing_stalk :
    Regular X ↔ IsLocallyNoetherian X ∧ ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) := sorry

/-- A scheme is regular exactly when it is locally Noetherian and its stalks at closed points are
regular local rings. -/
theorem regular_iff_closedPointStalk :
    Regular X ↔
      IsLocallyNoetherian X ∧
        ∀ x : X, x ∈ closedPoints X → IsRegularLocalRing (X.presheaf.stalk x) := sorry

end AlgebraicGeometry.Scheme
