/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal

/-!
# Étale-local properties of morphisms of algebraic spaces

A property of morphisms of schemes that is étale local on source-and-target
lifts to morphisms of algebraic spaces by requiring the original property on
the top arrow of every commutative square with étale vertical arrows from
schemes. If the original property is stable under composition, so is its lift.

A property of morphisms of schemes that is étale local on the target lifts to a
morphism of algebraic spaces by asking that every étale scheme pullback of the
morphism has the original property. For representable morphisms this may
equivalently be tested on a single surjective étale scheme pullback.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The source-and-target étale-local lift of a scheme-morphism property `P`:
every commutative square with étale vertical arrows from schemes has top arrow
satisfying `P`. -/
def etaleLocal {S : Scheme.{u}} (P : MorphismProperty Scheme.{u})
    [IsEtaleLocalAtSourceAndTarget P] : MorphismProperty (AlgebraicSpace S) :=
  fun {X Y} f =>
    ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
      (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
      (over (@AlgebraicGeometry.Etale)).presheaf a →
        (over (@AlgebraicGeometry.Etale)).presheaf b →
          a ≫ f = yoneda.map h ≫ b → P h.left

/-- A morphism of algebraic spaces has the source-and-target étale-local lift
of `P` if and only if every commutative square with étale vertical arrows from
schemes has top arrow satisfying `P`. -/
theorem etaleLocal_iff {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    [IsEtaleLocalAtSourceAndTarget P] {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    etaleLocal P f ↔
      ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
        (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf a →
          (over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = yoneda.map h ≫ b → P h.left := sorry

/-- The top arrow of an étale scheme square over a morphism having the
source-and-target étale-local lift of `P` satisfies `P`. -/
theorem etaleLocal_spec {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    [IsEtaleLocalAtSourceAndTarget P] {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : etaleLocal P f) {U V : Over S}
    (a : yoneda.obj U ⟶ X.functorOfPoints) (b : yoneda.obj V ⟶ Y.functorOfPoints)
    (h : U ⟶ V) (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = yoneda.map h ≫ b) : P h.left := sorry

/-- The composite of two morphisms with the source-and-target étale-local lift
of a composition-stable scheme-morphism property `P` has that lift. -/
theorem etaleLocal.comp {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    [IsEtaleLocalAtSourceAndTarget P] [P.IsStableUnderComposition]
    {X Y Z : AlgebraicSpace S} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : etaleLocal P f) (hg : etaleLocal P g) :
    etaleLocal P (f ≫ g) := sorry

/-- The source-and-target étale-local lift of a composition-stable
scheme-morphism property is stable under composition. -/
instance etaleLocal_isStableUnderComposition {S : Scheme.{u}}
    (P : MorphismProperty Scheme.{u}) [IsEtaleLocalAtSourceAndTarget P]
    [P.IsStableUnderComposition] :
    (etaleLocal P : MorphismProperty (AlgebraicSpace S)).IsStableUnderComposition := sorry

/-- The lift of a scheme-morphism property `P` that is étale local on the target
to a morphism of algebraic spaces over `S`: every represented pullback along an
étale morphism from a scheme to the target has the original property. -/
def etaleLocalOnTarget {S : Scheme.{u}} (P : MorphismProperty Scheme.{u})
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  ∀ {V W : Over S} (b : yoneda.obj V ⟶ Y.functorOfPoints)
    (fst : yoneda.obj W ⟶ X.functorOfPoints) (snd : W ⟶ V),
    (over (@AlgebraicGeometry.Etale)).presheaf b →
      IsPullback fst (yoneda.map snd) f b → P snd.left

/-- A morphism of algebraic spaces has the étale-on-target lift of `P` if and
only if every represented pullback along an étale morphism from a scheme to the
target has property `P`. -/
theorem etaleLocalOnTarget_iff {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    etaleLocalOnTarget P f ↔
      ∀ {V W : Over S} (b : yoneda.obj V ⟶ Y.functorOfPoints)
        (fst : yoneda.obj W ⟶ X.functorOfPoints) (snd : W ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf b →
          IsPullback fst (yoneda.map snd) f b → P snd.left := sorry

namespace etaleLocalOnTarget

/-- A universal étale-on-target represented-pullback condition witnesses
`etaleLocalOnTarget P f`. -/
theorem of {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : ∀ {V W : Over S} (b : yoneda.obj V ⟶ Y.functorOfPoints)
      (fst : yoneda.obj W ⟶ X.functorOfPoints) (snd : W ⟶ V),
      (over (@AlgebraicGeometry.Etale)).presheaf b →
        IsPullback fst (yoneda.map snd) f b → P snd.left) :
    etaleLocalOnTarget P f := sorry

/-- Under `etaleLocalOnTarget P f`, every étale-on-target represented pullback of
`f` has property `P` on the projection. -/
theorem spec {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} (h : etaleLocalOnTarget P f) :
    ∀ {V W : Over S} (b : yoneda.obj V ⟶ Y.functorOfPoints)
      (fst : yoneda.obj W ⟶ X.functorOfPoints) (snd : W ⟶ V),
      (over (@AlgebraicGeometry.Etale)).presheaf b →
        IsPullback fst (yoneda.map snd) f b → P snd.left := sorry

/-- An étale-on-target represented pullback of a morphism with the lift of `P`
has property `P` on the projection. -/
theorem apply {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} (h : etaleLocalOnTarget P f)
    {V W : Over S} (b : yoneda.obj V ⟶ Y.functorOfPoints)
    (fst : yoneda.obj W ⟶ X.functorOfPoints) (snd : W ⟶ V)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (hpb : IsPullback fst (yoneda.map snd) f b) : P snd.left := sorry

/-- For an isomorphism-invariant property `P` and a representable morphism, the
étale-on-target lift of `P` is equivalent to `P` holding on the chosen
represented pullback projections `hf.snd b`. -/
theorem iff_property_snd {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    [P.RespectsIso] {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    etaleLocalOnTarget P f ↔
      ∀ {V : Over S} (b : yoneda.obj V ⟶ Y.functorOfPoints),
        (over (@AlgebraicGeometry.Etale)).presheaf b → P (hf.snd b).left := sorry

/-- There is an étale morphism from a scheme to the target which is étale-locally
surjective, together with a represented pullback whose projection has property
`P`. -/
def existsSurjectivePullback {S : Scheme.{u}} (P : MorphismProperty Scheme.{u})
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  ∃ (V W : Over S) (b : yoneda.obj V ⟶ Y.functorOfPoints)
    (fst : yoneda.obj W ⟶ X.functorOfPoints) (snd : W ⟶ V),
    (over (@AlgebraicGeometry.Etale)).presheaf b ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) b ∧
        IsPullback fst (yoneda.map snd) f b ∧ P snd.left

/-- `existsSurjectivePullback P f` is the existence of a surjective étale scheme
pullback of `f` whose projection has property `P`. -/
theorem existsSurjectivePullback_iff {S : Scheme.{u}}
    {P : MorphismProperty Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    existsSurjectivePullback P f ↔
      ∃ (V W : Over S) (b : yoneda.obj V ⟶ Y.functorOfPoints)
        (fst : yoneda.obj W ⟶ X.functorOfPoints) (snd : W ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf b ∧
          Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) b ∧
            IsPullback fst (yoneda.map snd) f b ∧ P snd.left := sorry

namespace existsSurjectivePullback

/-- A surjective étale scheme pullback of `f` whose projection has property `P`
witnesses `existsSurjectivePullback P f`. -/
theorem of {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} {V W : Over S}
    (b : yoneda.obj V ⟶ Y.functorOfPoints)
    (fst : yoneda.obj W ⟶ X.functorOfPoints) (snd : W ⟶ V)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (hs : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) b)
    (hpb : IsPullback fst (yoneda.map snd) f b) (hP : P snd.left) :
    existsSurjectivePullback P f := sorry

/-- A morphism satisfying `existsSurjectivePullback P f` admits a surjective
étale scheme pullback whose projection has property `P`. -/
theorem spec {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} (h : existsSurjectivePullback P f) :
    ∃ (V W : Over S) (b : yoneda.obj V ⟶ Y.functorOfPoints)
      (fst : yoneda.obj W ⟶ X.functorOfPoints) (snd : W ⟶ V),
      (over (@AlgebraicGeometry.Etale)).presheaf b ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) b ∧
          IsPullback fst (yoneda.map snd) f b ∧ P snd.left := sorry

end existsSurjectivePullback

/-- If `X` and `Y` are representable, then some surjective étale scheme pullback
of the induced morphism of algebraic spaces has property `P` if and only if the
underlying scheme morphism has `P`. -/
theorem existsSurjectivePullback_ofOverMap_iff {S : Scheme.{u}}
    {P : MorphismProperty Scheme.{u}}
    [P.IsLocalAtTarget Scheme.etalePrecoverage] {U V : Over S} (h : U ⟶ V) :
    existsSurjectivePullback P (X := ofOver U) (Y := ofOver V) (yoneda.map h) ↔ P h.left := sorry

end etaleLocalOnTarget

/-- A representable morphism of algebraic spaces over `S` has
the étale-on-target lift of `P` if and only if some commutative diagram with
étale `V ⟶ Y` from a scheme and étale-locally surjective atlas has projection
`X ×_Y V ⟶ V` satisfying `P`. -/
theorem etaleLocalOnTarget_iff_existsSurjectivePullback {S : Scheme.{u}}
    {P : MorphismProperty Scheme.{u}}
    [P.IsLocalAtTarget Scheme.etalePrecoverage]
    {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    etaleLocalOnTarget P f ↔ etaleLocalOnTarget.existsSurjectivePullback P f := sorry

/-- For algebraic spaces represented by schemes, the étale-on-target
lift of `P` on the induced morphism of algebraic spaces is equivalent to the
underlying scheme morphism having `P`. -/
theorem etaleLocalOnTarget_ofOverMap_iff {S : Scheme.{u}}
    {P : MorphismProperty Scheme.{u}}
    [P.IsLocalAtTarget Scheme.etalePrecoverage] {U V : Over S} (h : U ⟶ V) :
    etaleLocalOnTarget P (X := ofOver U) (Y := ofOver V) (yoneda.map h) ↔ P h.left := sorry

end AlgebraicGeometry.AlgebraicSpace
