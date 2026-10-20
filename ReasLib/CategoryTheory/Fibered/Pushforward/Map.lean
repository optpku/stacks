module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Basic
public import ReasLib.CategoryTheory.Fibered.Pushforward
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of pushforward for fibered categories

The localized pushforward is functorial for strict cartesian based functors over its source
base.  The source-level map is induced by the general categorical-pullback functoriality API,
so this module does not duplicate a componentwise pullback construction.

The owner order is `sourceMapTransform` → `sourceMap` → `map`: the first two are concrete
prelocalized data, while `map` is the localization lift parameterized by a Prop-valued inversion
certificate.  `Map/TwoCell` adds the action on vertical transformations, and `Map/Fibered` adds
the fixed-owner endpoint choices.  The pseudofunctor leaves should be imported only after this
map layer is available.
-/

@[expose] public section

universe uC uD uS uT vC vD vS vT

namespace CategoryTheory

open Limits
open scoped Functor

namespace Functor.Pushforward

variable {C : Type uC} {D : Type uD}
variable {S : Type uS} {T : Type uT}
variable [Category.{vC} C] [Category.{vD} D]
variable [Category.{vS} S] [Category.{vT} T]

/-- The cospan transformation whose categorical-pullback map is the source-level pushforward
map induced by a cartesian based functor. -/
@[stacks 04WI "prelocalized pushforward cospan transform"]
def sourceMapTransform (u : C ⥤ D) {p : S ⥤ C} {q : T ⥤ C}
    (F : CartesianBasedFunctor p q) :
    CatCospanTransform (Comma.snd (𝟭 D) u) p (Comma.snd (𝟭 D) u) q where
  left := 𝟭 _
  base := 𝟭 C
  right := F.toFunctor
  squareLeft :=
    { iso := Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm }
  squareRight :=
    { iso := Functor.rightUnitor p ≪≫ F.toBasedFunctor.projectionIso.symm }

/-- Lemma 8.12.8 (tag 04WI): the map of prelocalized pushforward sources induced by a
cartesian based functor over `C`. -/
@[stacks 04WI "prelocalized pushforward map"]
def sourceMap (u : C ⥤ D) {p : S ⥤ C} {q : T ⥤ C}
    (F : CartesianBasedFunctor p q) : u ₚₚ p ⥤ u ₚₚ q :=
  CategoricalPullback.map (sourceMapTransform u F)

/-- The first pullback component of a source pushforward map is unchanged. -/
@[simp, stacks 04WI "prelocalized pushforward object comma component"]
theorem sourceMap.obj.fst (u : C ⥤ D) {p : S ⥤ C} {q : T ⥤ C}
    (F : CartesianBasedFunctor p q) (A : u ₚₚ p) :
    ((sourceMap u F).obj A).fst = A.fst := sorry

/-- The second pullback component of a source pushforward map is the image under the input
cartesian based functor. -/
@[simp, stacks 04WI "prelocalized pushforward object source component"]
theorem sourceMap.obj.snd (u : C ⥤ D) {p : S ⥤ C} {q : T ⥤ C}
    (F : CartesianBasedFunctor p q) (A : u ₚₚ p) :
    ((sourceMap u F).obj A).snd = F.toFunctor.obj A.snd := sorry

/-- The first morphism component of a source pushforward map is unchanged. -/
@[simp, stacks 04WI "prelocalized pushforward morphism comma component"]
theorem sourceMap.map.fst (u : C ⥤ D) {p : S ⥤ C} {q : T ⥤ C}
    (F : CartesianBasedFunctor p q) {A B : u ₚₚ p} (f : A ⟶ B) :
    ((sourceMap u F).map f).fst = f.fst := sorry

/-- The second morphism component of a source pushforward map is the image under the input
cartesian based functor. -/
@[simp, stacks 04WI "prelocalized pushforward morphism source component"]
theorem sourceMap.map.snd (u : C ⥤ D) {p : S ⥤ C} {q : T ⥤ C}
    (F : CartesianBasedFunctor p q) {A B : u ₚₚ p} (f : A ⟶ B) :
    ((sourceMap u F).map f).snd = F.toFunctor.map f.snd := sorry

/-- The source-level pushforward map commutes strictly with the projections to `D`. -/
@[stacks 04WI "prelocalized pushforward projection compatibility"]
theorem sourceMap.compSourceProjection (u : C ⥤ D) {p : S ⥤ C} {q : T ⥤ C}
    (F : CartesianBasedFunctor p q) :
    sourceMap u F ⋙ sourceProjection u q = sourceProjection u p := sorry

/-- A source-level pushforward map preserves vertical morphisms for the source projections. -/
@[stacks 04WI "prelocalized pushforward vertical preservation"]
theorem sourceMap.mapsVertical (u : C ⥤ D) {p : S ⥤ C} {q : T ⥤ C}
    (F : CartesianBasedFunctor p q) {A B : u ₚₚ p} {f : A ⟶ B}
    (hf : (sourceProjection u p).verticalMorphisms f) :
    (sourceProjection u q).verticalMorphisms ((sourceMap u F).map f) := sorry

/-- A source-level pushforward map preserves the strongly cartesian condition on the second
categorical-pullback component. -/
@[stacks 04WI "prelocalized pushforward strong cartesian preservation"]
theorem sourceMap.mapsStronglyCartesian
    (u : C ⥤ D) {p : S ⥤ C} {q : T ⥤ C}
    (F : CartesianBasedFunctor p q) {A B : u ₚₚ p} {f : A ⟶ B}
    (hf : p.IsStronglyCartesian (p.map f.snd) f.snd) :
    q.IsStronglyCartesian
      (q.map ((sourceMap u F).map f).snd) ((sourceMap u F).map f).snd := sorry

/-- A source-level pushforward map sends the vertical strongly-cartesian fraction property to
the corresponding fraction property. -/
@[stacks 04WI "prelocalized pushforward fraction preservation"]
theorem sourceMap.mapsFractions (u : C ⥤ D) {p : S ⥤ C} {q : T ⥤ C}
    (F : CartesianBasedFunctor p q) {A B : u ₚₚ p} (f : A ⟶ B)
    (hf : u.pushforwardFractions p f) :
    u.pushforwardFractions q ((sourceMap u F).map f) := sorry

/-- The proposition that the source-level pushforward map induces a map after localization. -/
@[stacks 04WI "prelocalized pushforward inversion predicate"]
def sourceMap.inverts (u : C ⥤ D) {p : S ⥤ C} {q : T ⥤ C}
    (F : CartesianBasedFunctor p q) : Prop :=
  (u.pushforwardFractions p).IsInvertedBy
    (sourceMap u F ⋙ (u.pushforwardFractions q).Q)

/-- The source-level pushforward map followed by localization inverts the source fraction
property. -/
@[stacks 04WI "canonical source-map inversion"]
theorem sourceMap.inverts.spec (u : C ⥤ D) {p : S ⥤ C} {q : T ⥤ C}
    (F : CartesianBasedFunctor p q) :
    sourceMap.inverts u F := sorry

/-- A specified fraction-inversion proof for every cartesian based functor between two fixed
projections. Supplying this owner explicitly keeps Hom-functor data independent of unfinished
proofs of the canonical inversion theorem. -/
@[stacks 04WI "raw pushforward inversion family"]
structure InversionChoice (u : C ⥤ D) (p : S ⥤ C) (q : T ⥤ C) : Prop where
  /-- The chosen source-fraction inversion proof for a cartesian based functor. -/
  inverts (F : CartesianBasedFunctor p q) : sourceMap.inverts u F

attribute [stacks 04WI "raw pushforward map inversion field"]
  Functor.Pushforward.InversionChoice.inverts

/-- The canonical inversion family for all cartesian based functors between two fixed
projections. -/
@[stacks 04WI "canonical raw pushforward inversion family"]
theorem InversionChoice.canonical (u : C ⥤ D) (p : S ⥤ C) (q : T ⥤ C) :
    InversionChoice u p q := sorry

/-- Lemma 8.12.8 (tag 04WI): the localized pushforward map induced by a cartesian based
functor and an explicit proof that its source-level map inverts the source fractions.  Keeping
that proof as an input prevents an unfinished proof obligation from entering the computational
localization map. -/
@[stacks 04WI "localized pushforward map"]
noncomputable def map (u : C ⥤ D) {p : S ⥤ C} {q : T ⥤ C}
    (F : CartesianBasedFunctor p q)
    (hF : sourceMap.inverts u F) :
    u ₚ p ⥤ u ₚ q :=
  Localization.Construction.lift
    (sourceMap u F ⋙ (u.pushforwardFractions q).Q)
    hF

/-- The localized pushforward map determined by a raw inversion choice.  This is a thin bridge over
`map`, so callers that already own the proof family need not unpack its field. -/
@[stacks 04WI "pushforward map from inversion choice"]
noncomputable def map.ofInversionChoice
    (u : C ⥤ D) {p : S ⥤ C} {q : T ⥤ C}
    (F : CartesianBasedFunctor p q)
    (h : InversionChoice u p q) :
    u ₚ p ⥤ u ₚ q :=
  map u F (h.inverts F)

/-- An explicitly certified pushforward map is the concrete localization lift of its
source-level map. -/
@[stacks 04WI "localized pushforward lifting owner"]
noncomputable instance map.lifting
    (u : C ⥤ D) {p : S ⥤ C} {q : T ⥤ C}
    (F : CartesianBasedFunctor p q) (hF : sourceMap.inverts u F) :
    Localization.Lifting (u.pushforwardFractions p).Q (u.pushforwardFractions p)
      (sourceMap u F ⋙ (u.pushforwardFractions q).Q) (map u F hF) :=
  Localization.liftingConstructionLift
    (sourceMap u F ⋙ (u.pushforwardFractions q).Q) hF

/-- The canonical localization-lifting isomorphism for an explicitly certified pushforward
map. Unlike an equality theorem used through `eqToHom`, this owner is supplied by the concrete
localization construction itself. -/
@[stacks 04WI "localized pushforward comparison isomorphism"]
noncomputable abbrev map.comparisonIso
    (u : C ⥤ D) {p : S ⥤ C} {q : T ⥤ C}
    (F : CartesianBasedFunctor p q) (hF : sourceMap.inverts u F) :
    (u.pushforwardFractions p).Q ⋙ map u F hF ≅
      sourceMap u F ⋙ (u.pushforwardFractions q).Q :=
  Localization.Lifting.iso
    (u.pushforwardFractions p).Q (u.pushforwardFractions p)
    (sourceMap u F ⋙ (u.pushforwardFractions q).Q) (map u F hF)

/-- The localized pushforward map is characterized on the canonical localization functor by
the source-level pushforward map. -/
@[stacks 04WI "localized pushforward localization comparison"]
theorem map.compQ (u : C ⥤ D) {p : S ⥤ C} {q : T ⥤ C}
    (F : CartesianBasedFunctor p q)
    (hF : sourceMap.inverts u F) :
    (u.pushforwardFractions p).Q ⋙ map u F hF =
      sourceMap u F ⋙ (u.pushforwardFractions q).Q := sorry

/-- The localized pushforward map commutes strictly with the canonical projections to `D`. -/
@[stacks 04WI "localized pushforward projection compatibility"]
theorem map.compProjection (u : C ⥤ D) {p : S ⥤ C} {q : T ⥤ C}
    (hp : ProjectionChoice u p) (hq : ProjectionChoice u q)
    (F : CartesianBasedFunctor p q)
    (hF : sourceMap.inverts u F) :
    map u F hF ⋙ u.pushforwardProjection q hq = u.pushforwardProjection p hp := sorry

/-- Under the finite-limit hypotheses for pushforward, the localized pushforward map preserves
strongly cartesian morphisms. -/
@[stacks 04WI "localized pushforward strong cartesian preservation"]
theorem map.preservesStronglyCartesian (u : C ⥤ D) {p : S ⥤ C} {q : T ⥤ C}
    (hp : ProjectionChoice u p) (hq : ProjectionChoice u q)
    (F : CartesianBasedFunctor p q)
    (hF : sourceMap.inverts u F) [p.IsFibered] [q.IsFibered]
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    (BasedFunctor.ofFunctor (map u F hF)
      (map.compProjection u hp hq F hF)).PreservesStronglyCartesian := sorry

end Functor.Pushforward

end CategoryTheory

-- Data audit: the localization functor and its comparison isomorphism receive `hF` explicitly;
-- neither definition consumes `sourceMap.inverts.spec`.
