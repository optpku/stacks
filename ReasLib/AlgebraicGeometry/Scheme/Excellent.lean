/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GScheme
public import ReasLib.AlgebraicGeometry.Scheme.J2.Locality
public import ReasLib.AlgebraicGeometry.Scheme.LocalRingProperty.Basic
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Locality
public import ReasLib.RingTheory.Excellent

/-!
# Excellent and quasi-excellent schemes

A scheme is (quasi-)excellent when the corresponding ring property holds on an affine open
neighbourhood of every point. Excellence is equivalent to quasi-excellence together with
universal catenarity.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme is quasi-excellent if every point admits an affine open neighbourhood whose ring of
sections is a quasi-excellent ring. -/
abbrev QuasiExcellent (X : Scheme.{u}) : Prop :=
  X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsQuasiExcellentRing.{u, u} A)

/-- A scheme is excellent if every point admits an affine open neighbourhood whose ring of
sections is an excellent ring. -/
abbrev Excellent (X : Scheme.{u}) : Prop :=
  X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsExcellentRing.{u, u} A)

/-- On a quasi-excellent scheme, every point lies in an affine open neighbourhood with
quasi-excellent coordinate ring. -/
theorem exists_affineOpen_quasiExcellentRing (X : Scheme.{u}) [QuasiExcellent X] (x : X) :
    ∃ U : X.affineOpens, x ∈ U ∧ IsQuasiExcellentRing.{u, u} (Γ(X, U)) :=
  HasRingPropertyLocally.exists_affineOpen X
    (fun A : CommRingCat.{u} ↦ IsQuasiExcellentRing.{u, u} A) x

/-- A scheme is quasi-excellent exactly when every point has an affine open neighbourhood with
quasi-excellent coordinate ring. -/
theorem quasiExcellent_iff (X : Scheme.{u}) :
    QuasiExcellent X ↔
      ∀ x : X, ∃ U : X.affineOpens, x ∈ U ∧ IsQuasiExcellentRing.{u, u} (Γ(X, U)) :=
  hasRingPropertyLocally_iff X (fun A : CommRingCat.{u} ↦ IsQuasiExcellentRing.{u, u} A)

/-- On an excellent scheme, every point lies in an affine open neighbourhood with excellent
coordinate ring. -/
theorem exists_affineOpen_excellentRing (X : Scheme.{u}) [Excellent X] (x : X) :
    ∃ U : X.affineOpens, x ∈ U ∧ IsExcellentRing.{u, u} (Γ(X, U)) :=
  HasRingPropertyLocally.exists_affineOpen X
    (fun A : CommRingCat.{u} ↦ IsExcellentRing.{u, u} A) x

/-- A scheme is excellent exactly when every point has an affine open neighbourhood with
excellent coordinate ring. -/
theorem excellent_exists_affineOpen_iff (X : Scheme.{u}) :
    Excellent X ↔
      ∀ x : X, ∃ U : X.affineOpens, x ∈ U ∧ IsExcellentRing.{u, u} (Γ(X, U)) :=
  hasRingPropertyLocally_iff X (fun A : CommRingCat.{u} ↦ IsExcellentRing.{u, u} A)

/-- An excellent scheme is quasi-excellent. -/
instance instQuasiExcellentOfExcellent {X : Scheme.{u}} [Excellent X] : QuasiExcellent X := sorry

/-- A quasi-excellent scheme is locally Noetherian. -/
instance instIsLocallyNoetherianOfQuasiExcellent {X : Scheme.{u}} [QuasiExcellent X] :
    IsLocallyNoetherian X := sorry

/-- An excellent scheme is universally catenary. -/
instance instUniversallyCatenaryOfExcellent {X : Scheme.{u}} [Excellent X] :
    UniversallyCatenary X := sorry

/-- A quasi-excellent universally catenary scheme is excellent. -/
instance Excellent.of_quasiExcellent {X : Scheme.{u}} [QuasiExcellent X] [UniversallyCatenary X] :
    Excellent X := sorry

/-- A scheme is excellent if and only if it is quasi-excellent and universally catenary. -/
theorem excellent_iff (X : Scheme.{u}) :
    Excellent X ↔ QuasiExcellent X ∧ UniversallyCatenary X := sorry

/-- A scheme is quasi-excellent if and only if it is a G-scheme and J-2. -/
@[stacks 0HA8]
theorem quasiExcellent_iff_gScheme_isJ2 (X : Scheme.{u}) :
    QuasiExcellent X ↔ GScheme X ∧ IsJ2 X := sorry

/-- A quasi-excellent scheme is a G-scheme. -/
instance instGSchemeOfQuasiExcellent {X : Scheme.{u}} [QuasiExcellent X] : GScheme X :=
  ((quasiExcellent_iff_gScheme_isJ2 X).mp inferInstance).1

/-- A quasi-excellent scheme is J-2. -/
instance instIsJ2OfQuasiExcellent {X : Scheme.{u}} [QuasiExcellent X] : IsJ2 X :=
  ((quasiExcellent_iff_gScheme_isJ2 X).mp inferInstance).2

/-- A G-scheme that is J-2 is quasi-excellent. -/
instance QuasiExcellent.of_gScheme {X : Scheme.{u}} [GScheme X] [IsJ2 X] :
    QuasiExcellent X :=
  (quasiExcellent_iff_gScheme_isJ2 X).mpr ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme
