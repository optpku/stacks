/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.Cleavage
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Bicategory
public import ReasLib.CategoryTheory.Fibered.StronglyCartesian.Property
public import ReasLib.CategoryTheory.Fibered.VerticalMorphism
public import ReasLib.CategoryTheory.Limits.FiniteNonempty

/-!
# Pushforward of fibered categories

For a functor `u : C ⥤ D` and a fibered category `p : S ⥤ C`, the pushforward `u ₚ S` is the
localization of the 2-fibre product `u ₚₚ S` at strongly-cartesian vertical morphisms.
This construction is independent of any topology or stack condition.

## Main declarations

* `CategoryTheory.Functor.pushforwardSource` — the prelocalized category `u ₚₚ S`.
* `CategoryTheory.Functor.pushforwardFractions` — the inverted morphism property.
* `CategoryTheory.Functor.pushforward` — the localized category `u ₚ S`.
* `CategoryTheory.Functor.Pushforward.ProjectionChoice` — raw projection certification.
* `CategoryTheory.Functor.Pushforward.projection` — the projection induced by an explicit
  fraction-inversion proof.
* `CategoryTheory.Functor.pushforwardProjection` — the projection `u ₚ S ⥤ D`.
* `CategoryTheory.FiberedCategoryOver.Pushforward.ProjectionChoice` — bundled fibred
  projection certification.
* `CategoryTheory.FiberedCategoryOver.pushforward` — the explicitly certified bundled
  pushforward.
-/

@[expose] public section

universe uC uD uS vC vD vS

namespace CategoryTheory

open Limits

namespace Functor

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

/-- The prelocalized pushforward category `u ₚₚ S`, the 2-fibre product of the comma projection
with `p`. -/
@[stacks 04WG "prelocalized pushforward source"]
abbrev pushforwardSource (u : C ⥤ D) (p : S ⥤ C) :=
  CategoricalPullback (Comma.snd (𝟭 D) u) p

/-- Notation: `u ₚₚ p` for the prelocalized pushforward source. -/
scoped infixr:100 " ₚₚ " => pushforwardSource

open scoped Functor

namespace Pushforward

/-- The projection from the prelocalized pushforward source to `D`, obtained from the left
component of the comma category. -/
@[stacks 04WG "prelocalized pushforward source projection"]
abbrev sourceProjection (u : C ⥤ D) (p : S ⥤ C) :
    u ₚₚ p ⥤ D :=
  CategoricalPullback.π₁ (Comma.snd (𝟭 D) u) p ⋙ Comma.fst (𝟭 D) u

/-- Verticality for the prelocalized source projection is equivalent to the component condition
that the left comma morphism is an identity transport. -/
@[stacks 04WG "prelocalized pushforward vertical criterion"]
theorem sourceProjection.vertical_iff (u : C ⥤ D) (p : S ⥤ C)
    {X Y : u ₚₚ p} (f : X ⟶ Y) :
    (sourceProjection u p).verticalMorphisms f ↔
      ∃ hV : X.fst.left = Y.fst.left, f.fst.left = eqToHom hV := sorry

end Pushforward

/-- The morphism property on `u ₚₚ S` selecting vertical strongly-cartesian morphisms. -/
@[stacks 04WF "pushforward fraction class"]
def pushforwardFractions (u : C ⥤ D) (p : S ⥤ C) :
    MorphismProperty (u ₚₚ p) :=
  (Pushforward.sourceProjection u p).verticalMorphisms ⊓
    (IsStronglyCartesian.property p).inverseImage
      (CategoricalPullback.π₂ (Comma.snd (𝟭 D) u) p)

/-- Membership in the pushforward denominator property means verticality for the source
projection together with strong cartesianness of the second categorical-pullback component. -/
@[stacks 04WF "pushforward fraction membership criterion"]
theorem pushforwardFractions.mem_iff (u : C ⥤ D) (p : S ⥤ C)
    {X Y : u ₚₚ p} (f : X ⟶ Y) :
    u.pushforwardFractions p f ↔
      (Pushforward.sourceProjection u p).verticalMorphisms f ∧
        p.IsStronglyCartesian (p.map f.snd) f.snd := sorry

namespace pushforwardFractions

/-- The pushforward denominator property contains identities and is closed under composition.
No finite-limit hypothesis is needed for this multiplicative part. -/
@[stacks 04WF "pushforward fraction multiplicativity"]
instance isMultiplicative (u : C ⥤ D) (p : S ⥤ C) :
    (u.pushforwardFractions p).IsMultiplicative := sorry

/-- If `p` is fibered, `C` has pullbacks and equalizers, and `u` preserves the corresponding
finite shapes, then the vertical strongly-cartesian morphisms in `u ₚₚ p` admit a right calculus
of fractions. This is the full right-multiplicative-system conclusion of Stacks 04WF. -/
@[stacks 04WF "pushforward fractions admit a right calculus"]
instance hasRightCalculus
    (u : C ⥤ D) (p : S ⥤ C) [p.IsFibered]
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    (u.pushforwardFractions p).HasRightCalculusOfFractions := sorry

end pushforwardFractions

/-- Lemma 8.12.6 (tag 04WG): the localized pushforward category `u ₚ S`. -/
@[stacks 04WG "localized pushforward category"]
abbrev pushforward (u : C ⥤ D) (p : S ⥤ C) :=
  (pushforwardFractions u p).Localization

/-- Notation: `u ₚ p` for the localized pushforward. -/
scoped infixr:100 " ₚ " => pushforward

namespace Pushforward

/-- The prelocalized projection inverts the vertical strongly-cartesian fraction property. -/
@[stacks 04WG "prelocalized pushforward projection inversion"]
theorem sourceProjection.invertsFractions (u : C ⥤ D) (p : S ⥤ C) :
    (u.pushforwardFractions p).IsInvertedBy (sourceProjection u p) := sorry

/-- An explicit choice certifying that the prelocalized pushforward projection descends through
the localization. Keeping this proof as an input prevents an unfinished existence theorem from
entering the localized projection functor. -/
@[stacks 04WG "raw pushforward projection choice"]
structure ProjectionChoice (u : C ⥤ D) (p : S ⥤ C) : Prop where
  /-- The source projection inverts every pushforward fraction. -/
  inverts : (u.pushforwardFractions p).IsInvertedBy (sourceProjection u p)

attribute [stacks 04WF "raw pushforward projection inversion field"]
  Functor.Pushforward.ProjectionChoice.inverts
attribute [stacks 04WG "raw pushforward projection inversion field"]
  Functor.Pushforward.ProjectionChoice.inverts

/-- The canonical raw projection choice supplied by the localization construction itself.

This named constructor is the default for ordinary consumers. The explicit projection-choice
parameter remains available for developments that need to pin a particular proof term or compare
two proof presentations.
-/
@[stacks 04WG "canonical raw pushforward projection choice"]
theorem ProjectionChoice.canonical (u : C ⥤ D) (p : S ⥤ C) :
    ProjectionChoice u p := sorry

/-- The projection from the localized pushforward induced by an explicit proof that the source
projection inverts the pushforward fractions. The inversion proof remains an input so
computational users can keep proof debt out of their concrete data. -/
@[stacks 04WG "localized pushforward projection"]
noncomputable def projection (u : C ⥤ D) (p : S ⥤ C)
    (h_inverts : (u.pushforwardFractions p).IsInvertedBy (sourceProjection u p)) :
    u ₚ p ⥤ D :=
  Localization.Construction.lift (sourceProjection u p) h_inverts

/-- The explicit pushforward projection is the canonical localization lifting of the source
projection. Registering this at its owner exposes the comparison isomorphism and its naturality
uniformly through `Localization.Lifting`. -/
@[stacks 04WG "localized pushforward projection lifting"]
noncomputable instance projection.lifting (u : C ⥤ D) (p : S ⥤ C)
    (h_inverts : (u.pushforwardFractions p).IsInvertedBy (sourceProjection u p)) :
    Localization.Lifting (u.pushforwardFractions p).Q (u.pushforwardFractions p)
      (sourceProjection u p) (projection u p h_inverts) :=
  Localization.liftingConstructionLift (sourceProjection u p) h_inverts

/-- The canonical localization-lifting isomorphism for an explicitly certified pushforward
projection.  This is the projection-level counterpart of `Functor.Pushforward.map.comparisonIso`;
unit and Hom constructions should reuse this owner instead of rebuilding `Localization.Lifting.iso`.
-/
@[stacks 04WG "localized pushforward projection comparison isomorphism"]
noncomputable abbrev projection.comparisonIso (u : C ⥤ D) (p : S ⥤ C)
    (h_inverts : (u.pushforwardFractions p).IsInvertedBy (sourceProjection u p)) :
    (u.pushforwardFractions p).Q ⋙ projection u p h_inverts ≅ sourceProjection u p :=
  Localization.Lifting.iso
    (u.pushforwardFractions p).Q (u.pushforwardFractions p)
    (sourceProjection u p) (projection u p h_inverts)

/-- The projection constructed from `h_inverts` restricts along the localization functor to the
source projection. -/
@[simp, stacks 04WG "localized pushforward projection computation"]
theorem Q.compProjection (u : C ⥤ D) (p : S ⥤ C)
    (h_inverts : (u.pushforwardFractions p).IsInvertedBy (sourceProjection u p)) :
    (u.pushforwardFractions p).Q ⋙ projection u p h_inverts = sourceProjection u p := sorry

end Pushforward

/-- The projection from the localized pushforward to `D`, formed from an explicit inversion
choice. -/
@[stacks 04WG "chosen localized pushforward projection"]
noncomputable abbrev pushforwardProjection (u : C ⥤ D) (p : S ⥤ C)
    (h : Pushforward.ProjectionChoice u p) :
    u ₚ p ⥤ D :=
  Pushforward.projection u p h.inverts

/-- An explicitly chosen pushforward projection restricts along the localization functor to the
prelocalized source projection. -/
@[simp, stacks 04WG "chosen pushforward projection computation"]
theorem Pushforward.Q.compPushforwardProjection (u : C ⥤ D) (p : S ⥤ C)
    (h : Pushforward.ProjectionChoice u p) :
    (u.pushforwardFractions p).Q ⋙ u.pushforwardProjection p h =
      Pushforward.sourceProjection u p := sorry

end Functor

namespace Functor

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

/-- Lemma 8.12.6 (tag 04WG): under the finite-limit hypotheses of Lemma 8.12.5, an explicitly
chosen localized pushforward projection is fibered. The projection type retains the supplied
choice `h`, so this instance reuses that choice rather than selecting new localization data. -/
@[stacks 04WG]
instance Pushforward.projectionIsFibered
    (u : C ⥤ D) (p : S ⥤ C) [p.IsFibered]
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (h : Pushforward.ProjectionChoice u p) :
    (u.pushforwardProjection p h).IsFibered := sorry

/-- The projection induced by an explicit fraction-inversion proof is fibered under the
finite-limit hypotheses for pushforward. This is a theorem rather than a global instance because
its projection depends on the explicitly supplied proof. -/
@[stacks 04WG "localized pushforward projection fibredness"]
theorem Pushforward.projection.isFibered
    (u : C ⥤ D) (p : S ⥤ C)
    (h_inverts : (u.pushforwardFractions p).IsInvertedBy (Pushforward.sourceProjection u p))
    [p.IsFibered] [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    (Pushforward.projection u p h_inverts).IsFibered := sorry

end Functor

namespace FiberedCategoryOver

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]

namespace Pushforward

/-- The explicit projection choice needed to bundle a localized pushforward as a fibred
category. It records both fraction inversion and fibredness of the resulting projection. -/
@[stacks 04WG "bundled pushforward projection choice"]
structure ProjectionChoice (u : C ⥤ D) (X : FiberedCategoryOver C) : Prop where
  /-- The prelocalized projection inverts the pushforward fractions. -/
  inverts : (u.pushforwardFractions X.p).IsInvertedBy
    (Functor.Pushforward.sourceProjection u X.p)
  /-- The explicitly induced localized projection is fibered. -/
  isFibered : (Functor.Pushforward.projection u X.p inverts).IsFibered

attribute [stacks 04WG "bundled pushforward fraction inversion field"]
  FiberedCategoryOver.Pushforward.ProjectionChoice.inverts
attribute [stacks 04WG "bundled pushforward fibredness field"]
  FiberedCategoryOver.Pushforward.ProjectionChoice.isFibered

/-- Forget a bundled projection choice to its raw fraction-inversion component. -/
@[stacks 04WG "raw pushforward projection choice"]
theorem ProjectionChoice.raw {u : C ⥤ D} {X : FiberedCategoryOver C}
    (h : ProjectionChoice u X) : Functor.Pushforward.ProjectionChoice u X.p := sorry

/-- Enrich a raw pushforward projection choice with an explicitly supplied proof that the
selected projection is fibered. -/
@[stacks 04WG "bundled pushforward choice from raw data"]
theorem ProjectionChoice.ofRawWith {u : C ⥤ D} (X : FiberedCategoryOver C)
    (h : Functor.Pushforward.ProjectionChoice u X.p)
    (h_fibered : (u.pushforwardProjection X.p h).IsFibered) : ProjectionChoice u X := sorry

/-- Enrich a raw pushforward projection choice using the canonical fibredness theorem for the
localized projection under the finite-limit hypotheses. -/
@[stacks 04WG "canonical bundled pushforward choice from raw data"]
theorem ProjectionChoice.ofRaw {u : C ⥤ D} (X : FiberedCategoryOver C)
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (h : Functor.Pushforward.ProjectionChoice u X.p) : ProjectionChoice u X := sorry

/-- The canonical bundled projection choice obtained from the raw localization choice and the
finite-limit fibredness theorem.
-/
@[stacks 04WG "canonical bundled pushforward projection choice"]
theorem ProjectionChoice.canonical (u : C ⥤ D) (X : FiberedCategoryOver C)
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    ProjectionChoice u X := sorry

end Pushforward

/-- The bundled fibred category obtained from the localized pushforward projection supplied by an
explicit choice. -/
@[stacks 04WG "bundled pushforward fibred category"]
noncomputable abbrev pushforward (u : C ⥤ D) (X : FiberedCategoryOver C)
    (h : Pushforward.ProjectionChoice u X) :
    FiberedCategoryOver D :=
  @FiberedCategoryOver.ofFunctor _ _ _ _
    (Functor.Pushforward.projection u X.p h.inverts) h.isFibered

/-- The total category of a bundled pushforward is the localization at the pushforward
fractions. -/
@[simp, stacks 04WG "bundled pushforward total computation"]
theorem pushforward.total (u : C ⥤ D) (X : FiberedCategoryOver C)
    (h : Pushforward.ProjectionChoice u X) :
    (pushforward u X h).total = Functor.pushforward u X.p := sorry

/-- The projection of the bundled pushforward is the explicitly chosen localized pushforward
projection. -/
@[simp, stacks 04WG "bundled pushforward projection computation"]
theorem pushforward.p (u : C ⥤ D) (X : FiberedCategoryOver C)
    (h : Pushforward.ProjectionChoice u X) :
    (pushforward u X h).p = Functor.Pushforward.projection u X.p h.inverts := sorry

end FiberedCategoryOver

end CategoryTheory

-- Expected audit: `ProjectionChoice` is Prop-valued, while its constructor theorems carry only
-- proof debt. The projection data declarations depend on their explicit choice argument, not on
-- the unfinished theorem `sourceProjection.invertsFractions`.
