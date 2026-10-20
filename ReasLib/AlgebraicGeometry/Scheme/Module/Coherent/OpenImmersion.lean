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
public import ReasLib.RingTheory.FormalFiber.PRing
public import ReasLib.RingTheory.FormalFiber.Serre
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Module

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

/-- On a Nagata universally catenary scheme, a coherent module on an open subscheme has
coherent pushforward if the reduced closure of every associated point has local dimension
at least two at each point outside the open subscheme. -/
theorem pushforward_obj_isCoherent_of_two_le_pointClosure_stalk
    {X : Scheme.{u}} [Nagata X] [UniversallyCatenary X]
    (U : X.Opens) (ℱ : (U : Scheme).Modules) [ℱ.IsCoherent]
    (hDim : ∀ x : U, x ∈ ℱ.associatedPoints → ∀ z : PointClosure.scheme (U.ι x),
      PointClosure.ι (U.ι x) z ∉ U →
        2 ≤ ringKrullDim ((PointClosure.scheme (U.ι x)).presheaf.stalk z)) :
    ((pushforward U.ι).obj ℱ).IsCoherent := sorry

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

/-- A coherent module on a locally Noetherian scheme has noncoherent pushforward when an
associated-point closure meets the boundary in local dimension at most one. -/
theorem pushforward_obj_not_isCoherent_of_pointClosure_stalk_dim_le_one
    {X : Scheme.{u}} [IsLocallyNoetherian X] (U : X.Opens)
    (ℱ : (U : Scheme).Modules) [ℱ.IsCoherent]
    (x : U) (hx : x ∈ ℱ.associatedPoints)
    (z : PointClosure.scheme (U.ι x)) (hz : PointClosure.ι (U.ι x) z ∉ U)
    (h_dimension :
      ringKrullDim ((PointClosure.scheme (U.ι x)).presheaf.stalk z) ≤ 1) :
    ¬ ((pushforward U.ι).obj ℱ).IsCoherent := sorry

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

end AlgebraicGeometry.Scheme.Modules
