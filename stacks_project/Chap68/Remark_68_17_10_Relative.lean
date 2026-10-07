module

public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import stacks_project.Chap68.Lemma_68_17_4_Relative
public import stacks_project.Chap68.Remark_68_17_10_VeryReasonable

/-!
# Relative object properties of morphisms of algebraic spaces

A morphism of algebraic spaces is relatively `P` when every scheme-base-change of
the source has object property `P`. This schema is identified with the existing
relative (β), decent, reasonable, and very reasonable morphism classes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X ⟶ Y` of algebraic spaces is relatively `P` if every
scheme-base-change of the source has object property `P`. -/
@[mk_iff]
class IsRelatively {S : Scheme.{u}} (P : ObjectProperty (AlgebraicSpace S))
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- The apex of an `IsPullback` square for `f` along a morphism from `ofOver T`
  has property `P`. -/
  of_isPullback {T : Over S} {W : AlgebraicSpace S} {g : ofOver T ⟶ Y}
    {pT : W ⟶ ofOver T} {pX : W ⟶ X} : IsPullback pT pX g f → P W

namespace IsRelatively

/-- The apex of a scheme-base-change square for a relatively `P` morphism has
property `P`. -/
theorem spec {S : Scheme.{u}} {P : ObjectProperty (AlgebraicSpace S)}
    {X Y W : AlgebraicSpace S} {f : X ⟶ Y} {T : Over S} {g : ofOver T ⟶ Y}
    {pT : W ⟶ ofOver T} {pX : W ⟶ X} [IsRelatively P f]
    (h : IsPullback pT pX g f) : P W := sorry

/-- A morphism is relatively `P` as soon as every scheme-base-change of the source
has property `P`. -/
theorem of {S : Scheme.{u}} {P : ObjectProperty (AlgebraicSpace S)}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : ∀ {T : Over S} {W : AlgebraicSpace S} {g : ofOver T ⟶ Y}
      {pT : W ⟶ ofOver T} {pX : W ⟶ X}, IsPullback pT pX g f → P W) :
    IsRelatively P f := sorry

/-- Relative conditions are monotone in the object property: if `P ≤ Q` and `f` is
relatively `P`, then `f` is relatively `Q`. -/
theorem mono {S : Scheme.{u}} {P Q : ObjectProperty (AlgebraicSpace S)}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} (hPQ : P ≤ Q)
    [IsRelatively P f] : IsRelatively Q f := sorry

end IsRelatively

/-- Relative property (β) is the scheme-base-change schema applied to the
object-level property (β). -/
theorem isRelatively_iff_propertyBeta {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} :
    IsRelatively (fun Z ↦ HasPropertyBeta Z) f ↔ PropertyBeta f := sorry

/-- Relative decency is the scheme-base-change schema applied to object-level
decency. -/
theorem isRelatively_iff_decent {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} :
    IsRelatively (fun Z ↦ IsDecent Z) f ↔ Decent f := sorry

/-- Relative reasonableness is the scheme-base-change schema applied to
object-level reasonableness. -/
theorem isRelatively_iff_reasonable {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} :
    IsRelatively (fun Z ↦ IsReasonable Z) f ↔ Reasonable f := sorry

/-- A morphism with property (β) is relatively of property (β). -/
instance instIsRelatively_of_propertyBeta {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [PropertyBeta f] :
    IsRelatively (fun Z ↦ HasPropertyBeta Z) f := sorry

/-- A decent morphism is relatively decent. -/
instance instIsRelatively_of_decent {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [Decent f] :
    IsRelatively (fun Z ↦ IsDecent Z) f := sorry

/-- A reasonable morphism is relatively reasonable. -/
instance instIsRelatively_of_reasonable {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [Reasonable f] :
    IsRelatively (fun Z ↦ IsReasonable Z) f := sorry

/-- The identity morphism of an algebraic space is relatively decent, via the
decent identity morphism. -/
instance instIsRelatively_id_isDecent {S : Scheme.{u}} {X : AlgebraicSpace S} :
    IsRelatively (fun Y ↦ IsDecent Y) (𝟙 X) :=
  instIsRelatively_of_decent

/-- Relative very reasonableness is exactly the scheme-base-change schema for the
source-defined object property, just as for the three preceding canonical conditions. -/
theorem isRelatively_iff_veryReasonable {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} :
    IsRelatively (fun Z ↦ IsVeryReasonable Z) f ↔ VeryReasonable f :=
  ⟨fun h ↦ ⟨fun hpb ↦ h.of_isPullback hpb⟩,
    fun h ↦ ⟨fun hpb ↦ h.ofOver_isPullback hpb⟩⟩

/-- A very reasonable morphism supplies the linked relative object-property schema. -/
instance instIsRelatively_of_veryReasonable {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [VeryReasonable f] : IsRelatively (fun Z ↦ IsVeryReasonable Z) f where
  of_isPullback h := VeryReasonable.ofOver_isPullback h

end AlgebraicGeometry.AlgebraicSpace
