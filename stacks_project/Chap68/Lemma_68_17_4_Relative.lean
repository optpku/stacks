module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap68.Definition_68_3_1_FiberDegree
public import stacks_project.Chap68.Lemma_68_12_8_Decent

/-!
# Relative property (β), decent, and reasonable morphisms

A morphism of algebraic spaces has property (β), is decent, or is reasonable when every
scheme-valued pullback of its source has the corresponding property as an algebraic space.
This module also records the missing space-level owners for property (β) and reasonableness.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space has property (β) if every point is represented by a monomorphism from
the spectrum of a field. -/
@[mk_iff]
class HasPropertyBeta {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop where
  /-- Every point arises from a monomorphism `Spec(K) ⟶ X`. -/
  exists_mono :
    ∀ x : Points X, ∃ p : FieldValuedPoint X, Mono p.hom ∧ Points.mk p = x

namespace HasPropertyBeta

/-- An algebraic space with property (β) has, at every point, a monomorphism from the spectrum
of a field representing that point. -/
theorem spec {S : Scheme.{u}} (X : AlgebraicSpace S) [HasPropertyBeta X] :
    ∀ x : Points X, ∃ p : FieldValuedPoint X, Mono p.hom ∧ Points.mk p = x :=
  sorry

/-- A choice of monomorphism `Spec(K) ⟶ X` at every point witnesses property (β). -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : ∀ x : Points X, ∃ p : FieldValuedPoint X, Mono p.hom ∧ Points.mk p = x) :
    HasPropertyBeta X :=
  sorry

end HasPropertyBeta

/-- A scheme over `S`, viewed as an algebraic space, has property (β). -/
instance instHasPropertyBeta_ofOver {S : Scheme.{u}} (T : Over S) :
    HasPropertyBeta (ofOver T) :=
  sorry

/-- An algebraic space is reasonable if every étale morphism from an affine scheme has
universally bounded fibres. -/
@[mk_iff]
class IsReasonable {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop where
  /-- Affine étale morphisms from schemes into `X` have universally bounded fibres. -/
  affine_etale_universallyBounded {U : Over S} (φ : ofOver U ⟶ X) [IsAffine U.left]
      [Etale φ] : universallyBoundedFibres φ

namespace IsReasonable

/-- A reasonable algebraic space has universally bounded fibres along every affine étale
morphism from a scheme. -/
theorem spec {S : Scheme.{u}} (X : AlgebraicSpace S) [IsReasonable X] {U : Over S}
    (φ : ofOver U ⟶ X) [IsAffine U.left] [Etale φ] : universallyBoundedFibres φ :=
  sorry

/-- An algebraic space is reasonable as soon as every affine étale morphism from a scheme has
universally bounded fibres. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : ∀ {U : Over S} (φ : ofOver U ⟶ X) [IsAffine U.left] [Etale φ],
      universallyBoundedFibres φ) : IsReasonable X :=
  sorry

end IsReasonable

/-- A scheme over `S`, viewed as an algebraic space, is reasonable. -/
instance instIsReasonable_ofOver {S : Scheme.{u}} (T : Over S) : IsReasonable (ofOver T) :=
  sorry

/-- A morphism of algebraic spaces has property (β) if every scheme-valued pullback of its
source has property (β). -/
@[mk_iff]
class PropertyBeta {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- The vertex of an `IsPullback` square against a scheme over `S` has property (β). -/
  ofOver_isPullback {T : Over S} {P : AlgebraicSpace S} {g : ofOver T ⟶ Y}
      {pT : P ⟶ ofOver T} {pX : P ⟶ X} :
    IsPullback pT pX g f → HasPropertyBeta P

namespace PropertyBeta

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

/-- Typeclass form of base-change stability for property (β) along a morphism for which the
pullback exists. -/
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

/-- Typeclass form of base-change stability for a decent morphism along a morphism for which
the pullback exists. -/
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

/-- Typeclass form of base-change stability for a reasonable morphism along a morphism for
which the pullback exists. -/
instance reasonable_pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [Reasonable f] [HasPullback f g] :
    Reasonable (pullback.snd f g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
