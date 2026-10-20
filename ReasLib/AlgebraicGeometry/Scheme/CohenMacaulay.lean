module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Noetherian.ClosedPoints
public import ReasLib.AlgebraicGeometry.Scheme.LocalRingProperty.Basic
public import ReasLib.RingTheory.CohenMacaulay.Ring

@[expose] public section

/-!
# Cohen-Macaulay schemes

A scheme is Cohen-Macaulay if every point admits an affine open neighborhood whose ring of
sections is Cohen-Macaulay. This file also records the pointwise criterion and local
Noetherianity of Cohen-Macaulay schemes.
-/

open AlgebraicGeometry
open TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- A scheme is Cohen-Macaulay if every point admits an affine open neighborhood whose coordinate
ring satisfies `CohenMacaulayRing`, which includes Noetherianity. -/
abbrev CohenMacaulay (X : Scheme.{u}) : Prop :=
  X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ CohenMacaulayRing A)

/-- On a Cohen-Macaulay scheme, every point lies in an affine open neighborhood with
Cohen-Macaulay coordinate ring. -/
theorem exists_affineOpen_cohenMacaulayRing [CohenMacaulay X] (x : X) :
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ CohenMacaulayRing (Γ(X, (U : X.Opens))) := by
  exact HasRingPropertyLocally.exists_affineOpen X
    (fun A : CommRingCat.{u} ↦ CohenMacaulayRing A) x

/-- Unfold `CohenMacaulay` into the affine-open neighborhood condition on points. -/
theorem cohenMacaulay_iff :
    CohenMacaulay X ↔
      ∀ x : X,
        ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ CohenMacaulayRing (Γ(X, (U : X.Opens))) := by
  exact hasRingPropertyLocally_iff X (fun A : CommRingCat.{u} ↦ CohenMacaulayRing A)

/-- A Cohen-Macaulay scheme is locally Noetherian. -/
noncomputable instance instIsLocallyNoetherianOfCohenMacaulay [CohenMacaulay X] :
    IsLocallyNoetherian X := by
  let hX : X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ CohenMacaulayRing A) :=
    inferInstance
  let U : X → X.affineOpens := fun x ↦ Classical.choose (hX.out x)
  have hU_mem : ∀ x : X, x ∈ ((U x : X.affineOpens) : X.Opens) := fun x ↦
    (Classical.choose_spec (hX.out x)).1
  have hU_cohenMacaulay :
      ∀ x : X, CohenMacaulayRing (Γ(X, ((U x : X.affineOpens) : X.Opens))) :=
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
    exact (hU_cohenMacaulay x).toIsNoetherian
  exact AlgebraicGeometry.isLocallyNoetherian_of_affine_cover hU_cover hU_noetherian

/-- Cohen-Macaulayness of a scheme is equivalent to local Noetherianity together with
Cohen-Macaulayness of every stalk, and it suffices to test the stalks at closed points. -/
theorem cohenMacaulay_tfae_stalk_and_closedPointStalk (X : Scheme.{u}) :
    List.TFAE
      [ CohenMacaulay X
      , IsLocallyNoetherian X ∧ ∀ x : X, CohenMacaulayRing (X.presheaf.stalk x)
      , IsLocallyNoetherian X ∧
          ∀ x : X, x ∈ closedPoints X → CohenMacaulayRing (X.presheaf.stalk x)
      ] := sorry

end AlgebraicGeometry.Scheme
