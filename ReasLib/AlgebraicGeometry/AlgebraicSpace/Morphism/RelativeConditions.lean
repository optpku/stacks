/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PropertyBeta
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reasonable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Relative conditions on morphisms of algebraic spaces

A morphism has property (β), is decent, or is reasonable when every pullback along
a morphism from a scheme has the corresponding property as an algebraic space.
Each condition is preserved under arbitrary base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces has property (β) if every scheme-valued pullback of its
source has property (β). -/
@[mk_iff]
class PropertyBeta {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- The vertex of an `IsPullback` square against a scheme over `S` has property (β). -/
  ofOver_isPullback {T : Over S} {P : AlgebraicSpace S} {g : ofOver T ⟶ Y}
      {pT : P ⟶ ofOver T} {pX : P ⟶ X} :
    IsPullback pT pX g f → HasPropertyBeta P

namespace PropertyBeta

/-- Every morphism from an algebraic space with property (β) has property (β). -/
@[instance 900]
instance of_hasPropertyBeta {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [HasPropertyBeta X] : PropertyBeta f :=
  sorry

/-- The identity morphism of an algebraic space has property (β). -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : PropertyBeta (𝟙 X) := sorry

/-- A morphism with property (β) pulls schemes back to algebraic spaces with property (β). -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} [PropertyBeta f]
    {T : Over S} {P : AlgebraicSpace S} {g : ofOver T ⟶ Y} {pT : P ⟶ ofOver T}
    {pX : P ⟶ X} (h : IsPullback pT pX g f) : HasPropertyBeta P :=
  sorry

/-- A morphism has property (β) as soon as every scheme-valued pullback of its source has
property (β). -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : ∀ {T : Over S} {P : AlgebraicSpace S} {g : ofOver T ⟶ Y} {pT : P ⟶ ofOver T}
      {pX : P ⟶ X}, IsPullback pT pX g f → HasPropertyBeta P) : PropertyBeta f :=
  sorry

/-- Morphisms with property (β) are stable under pullback along an arbitrary morphism,
expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S} {f : X ⟶ B}
    {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X} (sq : IsPullback f' g' g f)
    (hg : PropertyBeta g) : PropertyBeta g' :=
  sorry

/-- The base-change projection `pullback.snd f g` of a morphism with property (β) again has
property (β). -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : PropertyBeta f) (g : Z ⟶ Y) [HasPullback f g] :
    PropertyBeta (pullback.snd f g) :=
  sorry

end PropertyBeta

/-- The second projection of a pullback of a morphism with property (β) has property (β). -/
instance propertyBeta_pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [PropertyBeta f] [HasPullback f g] :
    PropertyBeta (pullback.snd f g) :=
  sorry

/-- A morphism of algebraic spaces is decent if every scheme-valued pullback of its source is
a decent algebraic space. -/
@[mk_iff]
class Decent {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- The vertex of an `IsPullback` square against a scheme over `S` is decent. -/
  ofOver_isPullback {T : Over S} {P : AlgebraicSpace S} {g : ofOver T ⟶ Y}
      {pT : P ⟶ ofOver T} {pX : P ⟶ X} : IsPullback pT pX g f → IsDecent P

namespace Decent

/-- Every morphism from a decent algebraic space is decent. -/
@[instance 900]
instance of_isDecent {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsDecent X] : Decent f :=
  sorry

/-- The identity morphism of an algebraic space is decent. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : Decent (𝟙 X) := sorry

/-- A decent morphism pulls schemes back to decent algebraic spaces. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} [Decent f]
    {T : Over S} {P : AlgebraicSpace S} {g : ofOver T ⟶ Y} {pT : P ⟶ ofOver T}
    {pX : P ⟶ X} (h : IsPullback pT pX g f) : IsDecent P :=
  sorry

/-- A morphism is decent as soon as every scheme-valued pullback of its source is decent. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : ∀ {T : Over S} {P : AlgebraicSpace S} {g : ofOver T ⟶ Y} {pT : P ⟶ ofOver T}
      {pX : P ⟶ X}, IsPullback pT pX g f → IsDecent P) : Decent f :=
  sorry

/-- Decent morphisms of algebraic spaces are stable under pullback along an arbitrary
morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S} {f : X ⟶ B}
    {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X} (sq : IsPullback f' g' g f)
    (hg : Decent g) : Decent g' :=
  sorry

/-- The base-change projection `pullback.snd f g` of a decent morphism is decent. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : Decent f) (g : Z ⟶ Y) [HasPullback f g] : Decent (pullback.snd f g) :=
  sorry

end Decent

/-- The second projection of a pullback of a decent morphism is decent. -/
instance decent_pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y)
    (g : Z ⟶ Y) [Decent f] [HasPullback f g] : Decent (pullback.snd f g) :=
  sorry

/-- A morphism of algebraic spaces is reasonable if every scheme-valued pullback of its source
is a reasonable algebraic space. -/
@[mk_iff]
class Reasonable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- The vertex of an `IsPullback` square against a scheme over `S` is reasonable. -/
  ofOver_isPullback {T : Over S} {P : AlgebraicSpace S} {g : ofOver T ⟶ Y}
      {pT : P ⟶ ofOver T} {pX : P ⟶ X} : IsPullback pT pX g f → IsReasonable P

namespace Reasonable

/-- Every morphism from a reasonable algebraic space is reasonable. -/
@[instance 900]
instance of_isReasonable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsReasonable X] : Reasonable f :=
  sorry

/-- The identity morphism of an algebraic space is reasonable. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : Reasonable (𝟙 X) := sorry

/-- A reasonable morphism pulls schemes back to reasonable algebraic spaces. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} [Reasonable f]
    {T : Over S} {P : AlgebraicSpace S} {g : ofOver T ⟶ Y} {pT : P ⟶ ofOver T}
    {pX : P ⟶ X} (h : IsPullback pT pX g f) : IsReasonable P :=
  sorry

/-- A morphism is reasonable as soon as every scheme-valued pullback of its source is
reasonable. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : ∀ {T : Over S} {P : AlgebraicSpace S} {g : ofOver T ⟶ Y} {pT : P ⟶ ofOver T}
      {pX : P ⟶ X}, IsPullback pT pX g f → IsReasonable P) : Reasonable f :=
  sorry

/-- Reasonable morphisms of algebraic spaces are stable under pullback along an arbitrary
morphism, expressed by an `IsPullback` square. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S} {f : X ⟶ B}
    {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X} (sq : IsPullback f' g' g f)
    (hg : Reasonable g) : Reasonable g' :=
  sorry

/-- The base-change projection `pullback.snd f g` of a reasonable morphism is reasonable. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : Reasonable f) (g : Z ⟶ Y) [HasPullback f g] :
    Reasonable (pullback.snd f g) :=
  sorry

end Reasonable

/-- The second projection of a pullback of a reasonable morphism is reasonable. -/
instance reasonable_pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [Reasonable f] [HasPullback f g] :
    Reasonable (pullback.snd f g) :=
  sorry

/-- Having property (β) is preserved under arbitrary base change. -/
instance propertyBeta_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@PropertyBeta _ : MorphismProperty (AlgebraicSpace S)) := sorry

/-- Being decent is preserved under arbitrary base change. -/
instance decent_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@Decent _ : MorphismProperty (AlgebraicSpace S)) := sorry

/-- Being reasonable is preserved under arbitrary base change. -/
instance reasonable_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@Reasonable _ : MorphismProperty (AlgebraicSpace S)) := sorry

end AlgebraicGeometry.AlgebraicSpace
