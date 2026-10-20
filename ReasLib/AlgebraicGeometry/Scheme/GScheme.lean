/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Data.List.TFAE
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.Scheme.LocalRing.Completion
public import ReasLib.AlgebraicGeometry.Scheme.LocalRingProperty.Basic
public import ReasLib.RingTheory.Regular.GRing

/-!
# G-schemes

A scheme is a G-scheme when the G-ring property holds on an affine open neighbourhood of every
point. This is independent of group actions: a G-scheme in this sense is not a scheme equipped
with an action of a finite group or group scheme.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme is a G-scheme if every point admits an affine open neighbourhood whose ring of
sections is a G-ring. This terminology is nonstandard: it does not mean a scheme equipped with an
action of a finite group or group scheme. -/
abbrev GScheme (X : Scheme.{u}) : Prop :=
  X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsGRing A)

/-- On a G-scheme, every point lies in an affine open neighbourhood with G-ring coordinate ring. -/
theorem exists_affineOpen_gRing (X : Scheme.{u}) [GScheme X] (x : X) :
    ∃ U : X.affineOpens, x ∈ U ∧ IsGRing (Γ(X, U)) :=
  HasRingPropertyLocally.exists_affineOpen X (fun A : CommRingCat.{u} ↦ IsGRing A) x

/-- A scheme is a G-scheme exactly when every point has an affine open neighbourhood with
G-ring coordinate ring. -/
theorem gScheme_iff (X : Scheme.{u}) :
    GScheme X ↔ ∀ x : X, ∃ U : X.affineOpens, x ∈ U ∧ IsGRing (Γ(X, U)) :=
  hasRingPropertyLocally_iff X (fun A : CommRingCat.{u} ↦ IsGRing A)

/-- A G-scheme is locally Noetherian, since G-rings are Noetherian. -/
instance instIsLocallyNoetherianOfGScheme {X : Scheme.{u}} [GScheme X] :
    IsLocallyNoetherian X := sorry

/-- A scheme is a G-scheme exactly when it is locally Noetherian with regular
stalk completion maps, equivalently when regularity is tested only at closed points. -/
theorem gScheme_tfae (X : Scheme.{u}) :
    List.TFAE [X.GScheme,
      IsLocallyNoetherian X ∧ ∀ x : X, (completedLocalMap X x).Regular,
      IsLocallyNoetherian X ∧ ∀ x : X,
        x ∈ closedPoints X → (completedLocalMap X x).Regular] := sorry

/-- A scheme is a G-scheme if and only if it is locally Noetherian and its
canonical stalk completion map is regular at every point. -/
theorem gScheme_iff_regular_completedLocalMap (X : Scheme.{u}) :
    GScheme X ↔
      IsLocallyNoetherian X ∧ ∀ x : X, (completedLocalMap X x).Regular :=
  (gScheme_tfae X).out 0 1

/-- A scheme is a G-scheme if and only if it is locally Noetherian and its
canonical stalk completion map is regular at every closed point. -/
theorem gScheme_iff_closedPoint_regular_completedLocalMap (X : Scheme.{u}) :
    GScheme X ↔
      IsLocallyNoetherian X ∧
        ∀ x : X, x ∈ closedPoints X → (completedLocalMap X x).Regular :=
  (gScheme_tfae X).out 0 2

/-- On a G-scheme, the completed local map at every point is regular. -/
instance instRegular_completedLocalMap {X : Scheme.{u}} [GScheme X] (x : X) :
    (completedLocalMap X x).Regular :=
  ((gScheme_iff_regular_completedLocalMap X).mp inferInstance).2 x

end AlgebraicGeometry.Scheme
