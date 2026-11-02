/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Union
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Basic
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Support
public import ReasLib.RingTheory.AdicCompletion.Noetherian
public import ReasLib.RingTheory.Completion.Dimension
public import ReasLib.RingTheory.FormalFiber.PRing
public import ReasLib.RingTheory.FormalFiber.Serre
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Module
public import ReasLib.RingTheory.Normal.Nagata.EssentialFiniteness
public import ReasLib.RingTheory.Normal.Nagata.FormalFiber
public import ReasLib.RingTheory.CohenMacaulay.SerreCondition.Reduced

/-!
# Coherent modules along open immersions

This file records a support criterion for coherence after pushforward along the inclusion of an
open subscheme.
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A coherent module supported on an ambient closed subset contained in an open subscheme has
coherent pushforward along the open inclusion. -/
theorem pushforward_obj_isCoherent_of_support_subset
    {X : Scheme.{u}} (U : X.Opens) (T : Closeds X)
    (hT : (T : Set X) ⊆ (U : Set X)) (ℱ : (U : Scheme).Modules) [ℱ.IsCoherent]
    (hSupp : RingedSpace.moduleSupportedOn (Subtype.val ⁻¹' (T : Set X)) ℱ) :
    ((pushforward U.ι).obj ℱ).IsCoherent := sorry

/-- For a coherent module on an open subscheme of a locally Noetherian scheme, its pushforward is
coherent exactly when the pushed-forward structure sheaf of every reduced associated-point
closure is coherent. -/
theorem pushforward_obj_isCoherent_iff_associatedPointClosures
    {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens)
    (ℱ : (U : Scheme).Modules) [ℱ.IsCoherent] :
    (∀ x : U, x ∈ ℱ.associatedPoints →
      ((pushforward U.ι).obj
        (closedSubschemeStructureSheafOn
          (Scheme.PointClosure.reducedStructure x).ideal)).IsCoherent) ↔
      ((pushforward U.ι).obj ℱ).IsCoherent := sorry

/-- On a universally catenary scheme whose boundary stalks have `(S₁)` formal fibers,
a coherent module on an open subscheme has coherent pushforward exactly when each
associated-point closure has local dimension at least two at every boundary point. -/
theorem pushforward_obj_isCoherent_iff_two_le_pointClosure_stalk_of_formalFibers
    {X : Scheme.{u}} [UniversallyCatenary X] (U : X.Opens)
    (ℱ : (U : Scheme).Modules) [ℱ.IsCoherent]
    (h_formal : ∀ z : X, z ∉ U →
      (FieldAlgebraProperty.serreConditionS 1).HoldsOnFormalFibers
        (X.presheaf.stalk z)) :
    ((pushforward U.ι).obj ℱ).IsCoherent ↔
      ∀ x : U, x ∈ ℱ.associatedPoints →
        ∀ y : PointClosure.scheme (U.ι x),
          PointClosure.ι (U.ι x) y ∉ U →
            2 ≤ ringKrullDim
              ((PointClosure.scheme (U.ι x)).presheaf.stalk y) := sorry

/-- On a Nagata universally catenary scheme, a coherent module on an open subscheme has
coherent pushforward if the reduced closure of every associated point has local dimension
at least two at each point outside the open subscheme. -/
theorem pushforward_obj_isCoherent_of_two_le_pointClosure_stalk
    {X : Scheme.{u}} [Nagata X] [UniversallyCatenary X]
    (U : X.Opens) (ℱ : (U : Scheme).Modules) [ℱ.IsCoherent]
    (hDim : ∀ x : U, x ∈ ℱ.associatedPoints → ∀ z : PointClosure.scheme (U.ι x),
      PointClosure.ι (U.ι x) z ∉ U →
        2 ≤ ringKrullDim ((PointClosure.scheme (U.ι x)).presheaf.stalk z)) :
    ((pushforward U.ι).obj ℱ).IsCoherent := by
  apply (pushforward_obj_isCoherent_iff_two_le_pointClosure_stalk_of_formalFibers U ℱ ?_).mpr hDim
  -- Nagata stalks have geometrically reduced, hence `(S₁)`, formal fibers.
  intro z _ q
  obtain ⟨V, hzV, hV⟩ :=
    Scheme.HasRingPropertyLocally.out (X := X) (P := fun A ↦ NagataRing A) z
  letI : NagataRing Γ(X, (V : X.Opens)) := hV
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨z, hzV⟩ : (V : X.Opens))
  letI := V.property.isLocalization_stalk ⟨z, hzV⟩
  letI : NagataRing (X.presheaf.stalk z) :=
    NagataRing.of_isLocalization (V.property.primeIdealOf ⟨z, hzV⟩).asIdeal.primeCompl
  let Ahat := AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
    (X.presheaf.stalk z)
  letI : Algebra.IsGeometricallyReduced q.asIdeal.ResidueField (q.asIdeal.Fiber Ahat) :=
    NagataRing.geometricallyReducedFormalFibers (X.presheaf.stalk z) q
  letI : _root_.IsReduced (q.asIdeal.Fiber Ahat) :=
    Algebra.isReduced_of_isGeometricallyReduced q.asIdeal.ResidueField
  letI : Algebra Ahat (q.asIdeal.Fiber Ahat) := Algebra.TensorProduct.rightAlgebra
  letI : IsNoetherianRing (q.asIdeal.Fiber Ahat) :=
    isNoetherianRing_of_ringEquiv _ (Ideal.Fiber.algEquivAux₁ q.asIdeal (S := Ahat)).symm.toRingEquiv
  exact inferInstanceAs (SerreConditionS (q.asIdeal.Fiber Ahat) 1)

/-- On an integral locally Noetherian scheme, the structure sheaf of a nonempty open
subscheme has coherent pushforward if every associated-prime quotient of the maximal-ideal-adic
completion of each boundary stalk has Krull dimension at least two. -/
theorem pushforward_structureSheaf_isCoherent_of_completion_associatedPrimes
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (U : X.Opens) [Nonempty U]
    (h_dimension : ∀ z : X, z ∉ U →
      let Ahat := AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
        (X.presheaf.stalk z)
      ∀ p ∈ associatedPrimesOfModule Ahat Ahat,
        2 ≤ ringKrullDim (Ahat ⧸ p)) :
    ((pushforward U.ι).obj
      (SheafOfModules.unit (U : Scheme).ringCatSheaf)).IsCoherent := sorry

/-- For a coherent module on an open subscheme of a locally Noetherian scheme, its pushforward
is coherent exactly when every associated-prime quotient of the completed stalk at a boundary
point of each reduced associated-point closure has Krull dimension at least two. -/
theorem pushforward_obj_isCoherent_iff_completion_associatedPrimes
    {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens)
    (ℱ : (U : Scheme).Modules) [ℱ.IsCoherent] :
    ((pushforward U.ι).obj ℱ).IsCoherent ↔
      ∀ x : U, x ∈ ℱ.associatedPoints →
        ∀ z : PointClosure.scheme (U.ι x),
          PointClosure.ι (U.ι x) z ∉ U →
            let Ahat :=
              AdicCompletion
                (IsLocalRing.maximalIdeal ((PointClosure.scheme (U.ι x)).presheaf.stalk z))
                ((PointClosure.scheme (U.ι x)).presheaf.stalk z)
            ∀ p ∈ associatedPrimesOfModule Ahat Ahat,
              2 ≤ ringKrullDim (Ahat ⧸ p) := sorry

/-- A coherent module on a locally Noetherian scheme has noncoherent pushforward when an
associated-point closure meets the boundary in local dimension at most one. -/
theorem pushforward_obj_not_isCoherent_of_pointClosure_stalk_dim_le_one
    {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens)
    (ℱ : (U : Scheme).Modules) [ℱ.IsCoherent]
    (x : U) (hx : x ∈ ℱ.associatedPoints)
    (z : PointClosure.scheme (U.ι x)) (hz : PointClosure.ι (U.ι x) z ∉ U)
    (h_dimension :
      ringKrullDim ((PointClosure.scheme (U.ι x)).presheaf.stalk z) ≤ 1) :
    ¬ ((pushforward U.ι).obj ℱ).IsCoherent := by
  intro hCoherent
  have hCompletion :=
    (pushforward_obj_isCoherent_iff_completion_associatedPrimes U ℱ).mp hCoherent x hx z hz
  letI : IsLocallyNoetherian (PointClosure.scheme (U.ι x)) :=
    LocallyOfFiniteType.isLocallyNoetherian (PointClosure.ι (U.ι x))
  let A := (PointClosure.scheme (U.ι x)).presheaf.stalk z
  let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
  -- A nonzero Noetherian completion has an associated prime, and its quotients
  -- cannot have dimension larger than the original local ring.
  obtain ⟨p, hp⟩ := associatedPrimes.nonempty Ahat Ahat
  have hp' : p ∈ associatedPrimesOfModule Ahat Ahat := by
    rw [associatedPrimesOfModule_eq_associatedPrimes]
    exact hp
  have hLower : 2 ≤ ringKrullDim (Ahat ⧸ p) := hCompletion p hp'
  have hUpper : ringKrullDim (Ahat ⧸ p) ≤ 1 := by
    calc
      ringKrullDim (Ahat ⧸ p) ≤ ringKrullDim Ahat := ringKrullDim_quotient_le p
      _ = ringKrullDim A := (AdicCompletion.ringKrullDim_eq A).symm
      _ ≤ 1 := h_dimension
  exact (by decide : ¬ (2 : WithBot ℕ∞) ≤ 1) (hLower.trans hUpper)

/-- On an integral Noetherian scheme, a one-dimensional associated component of a completed
boundary stalk obstructs coherence of the pushforward of the structure sheaf from a nonempty open.
-/
theorem pushforward_structureSheaf_not_isCoherent_of_dim_one
    {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    (U : X.Opens) [Nonempty U] (z : X) (hz : z ∉ U)
    (h_associated_dimension :
      let Ahat := AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
        (X.presheaf.stalk z)
      ∃ p ∈ associatedPrimesOfModule Ahat Ahat,
        ringKrullDim (Ahat ⧸ p) = 1) :
    ¬ ((pushforward U.ι).obj
      (SheafOfModules.unit (U : Scheme).ringCatSheaf)).IsCoherent := sorry

end AlgebraicGeometry.Scheme.Modules
