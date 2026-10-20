/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeConditions
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.VeryReasonable

/-!
# Relative object properties

A morphism has relative object property `P` when every scheme-base-change apex has
property `P`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X ⟶ Y` is relatively `P` if every scheme-base-change apex has `P`. -/
@[mk_iff]
class IsRelatively {S : Scheme.{u}} (P : ObjectProperty (AlgebraicSpace S))
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- The apex of a scheme-base-change pullback square has property `P`. -/
  of_isPullback {T : Over S} {W : AlgebraicSpace S} {g : ofOver T ⟶ Y}
    {pT : W ⟶ ofOver T} {pX : W ⟶ X} : IsPullback pT pX g f → P W

namespace IsRelatively

/-- The apex of a scheme-base-change square for a relatively `P` morphism has `P`. -/
theorem spec {S : Scheme.{u}} {P : ObjectProperty (AlgebraicSpace S)}
    {X Y W : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S} {g : ofOver T ⟶ Y}
    {pT : W ⟶ ofOver T} {pX : W ⟶ X} [IsRelatively P f]
    (h : IsPullback pT pX g f) : P W := sorry

/-- A morphism is relatively `P` when every scheme-base-change apex has `P`. -/
theorem of {S : Scheme.{u}} {P : ObjectProperty (AlgebraicSpace S)}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : ∀ {T : Over S} {W : AlgebraicSpace S} {g : ofOver T ⟶ Y}
      {pT : W ⟶ ofOver T} {pX : W ⟶ X}, IsPullback pT pX g f → P W) :
    IsRelatively P f := sorry

/-- Relative object properties are monotone in the object property. -/
theorem mono {S : Scheme.{u}} {P Q : ObjectProperty (AlgebraicSpace S)}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} (hPQ : P ≤ Q)
    [IsRelatively P f] : IsRelatively Q f := sorry

end IsRelatively

/-- Relative property (β) is the scheme-base-change schema for property (β). -/
theorem isRelatively_iff_propertyBeta {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} :
    IsRelatively (fun Z ↦ HasPropertyBeta Z) f ↔ PropertyBeta f := sorry

/-- Relative decency is the scheme-base-change schema for decency. -/
theorem isRelatively_iff_decent {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} :
    IsRelatively (fun Z ↦ IsDecent Z) f ↔ Decent f := sorry

/-- Relative reasonableness is the scheme-base-change schema for reasonableness. -/
theorem isRelatively_iff_reasonable {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} :
    IsRelatively (fun Z ↦ IsReasonable Z) f ↔ Reasonable f := sorry

/-- A morphism with property (β) is relatively of property (β). -/
instance instIsRelatively_of_propertyBeta {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [PropertyBeta f] :
    IsRelatively (fun Z ↦ HasPropertyBeta Z) f := sorry

/-- A decent morphism is relatively decent. -/
instance instIsRelatively_of_decent {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [Decent f] : IsRelatively (fun Z ↦ IsDecent Z) f := sorry

/-- A reasonable morphism is relatively reasonable. -/
instance instIsRelatively_of_reasonable {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [Reasonable f] : IsRelatively (fun Z ↦ IsReasonable Z) f := sorry

/-- The identity morphism is relatively decent. -/
instance instIsRelatively_id_isDecent {S : Scheme.{u}} {X : AlgebraicSpace S} :
    IsRelatively (fun Y ↦ IsDecent Y) (𝟙 X) := instIsRelatively_of_decent

/-- Relative very reasonableness is the scheme-base-change schema for the object property. -/
theorem isRelatively_iff_veryReasonable {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} :
    IsRelatively (fun Z ↦ IsVeryReasonable Z) f ↔ VeryReasonable f :=
  ⟨fun h ↦ ⟨fun hpb ↦ h.of_isPullback hpb⟩,
    fun h ↦ ⟨fun hpb ↦ h.ofOver_isPullback hpb⟩⟩

/-- A very reasonable morphism is relatively very reasonable. -/
instance instIsRelatively_of_veryReasonable {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [VeryReasonable f] :
    IsRelatively (fun Z ↦ IsVeryReasonable Z) f where
  of_isPullback h := VeryReasonable.ofOver_isPullback h

end AlgebraicGeometry.AlgebraicSpace
