/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocal
public import stacks_project.Chap66.Definition_66_4_1_Points

/-!
# Étale locality on the target for morphisms of algebraic spaces

The morphism-level étale-local predicates and their specification API are
provided by the shared mathematical owner. The represented-scheme check uses
`ofOverMap` for the scheme-induced morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- The lift of a scheme-morphism property `P` that is étale local on the target
to a morphism of algebraic spaces over `S`: every represented pullback along an
étale morphism from a scheme to the target has the original property. -/
#check (AlgebraicGeometry.AlgebraicSpace.etaleLocalOnTarget :
  ∀ {S : Scheme.{u}} (P : MorphismProperty Scheme.{u})
    {X Y : AlgebraicSpace S} (f : X ⟶ Y),
 Prop)

/- A morphism of algebraic spaces has the étale-on-target lift of `P` if and
only if every represented pullback along an étale morphism from a scheme to the
target has property `P`. -/
#check (AlgebraicGeometry.AlgebraicSpace.etaleLocalOnTarget_iff :
  ∀ {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y),

    etaleLocalOnTarget P f ↔
      ∀ {V W : Over S} (b : yoneda.obj V ⟶ Y.functorOfPoints)
        (fst : yoneda.obj W ⟶ X.functorOfPoints) (snd : W ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf b →
          IsPullback fst (yoneda.map snd) f b → P snd.left)

/- A universal étale-on-target represented-pullback condition witnesses
`etaleLocalOnTarget P f`. -/
#check (AlgebraicGeometry.AlgebraicSpace.etaleLocalOnTarget.of :
  ∀ {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : ∀ {V W : Over S} (b : yoneda.obj V ⟶ Y.functorOfPoints)
      (fst : yoneda.obj W ⟶ X.functorOfPoints) (snd : W ⟶ V),
      (over (@AlgebraicGeometry.Etale)).presheaf b →
        IsPullback fst (yoneda.map snd) f b → P snd.left),

    etaleLocalOnTarget P f)

/- Under `etaleLocalOnTarget P f`, every étale-on-target represented pullback of
`f` has property `P` on the projection. -/
#check (AlgebraicGeometry.AlgebraicSpace.etaleLocalOnTarget.spec :
  ∀ {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} (h : etaleLocalOnTarget P f),

    ∀ {V W : Over S} (b : yoneda.obj V ⟶ Y.functorOfPoints)
      (fst : yoneda.obj W ⟶ X.functorOfPoints) (snd : W ⟶ V),
      (over (@AlgebraicGeometry.Etale)).presheaf b →
        IsPullback fst (yoneda.map snd) f b → P snd.left)

/- An étale-on-target represented pullback of a morphism with the lift of `P`
has property `P` on the projection. -/
#check (AlgebraicGeometry.AlgebraicSpace.etaleLocalOnTarget.apply :
  ∀ {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} (h : etaleLocalOnTarget P f)
    {V W : Over S} (b : yoneda.obj V ⟶ Y.functorOfPoints)
    (fst : yoneda.obj W ⟶ X.functorOfPoints) (snd : W ⟶ V)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (hpb : IsPullback fst (yoneda.map snd) f b),
 P snd.left)

/- For an isomorphism-invariant property `P` and a representable morphism, the
étale-on-target lift of `P` is equivalent to `P` holding on the chosen
represented pullback projections `hf.snd b`. -/
#check (AlgebraicGeometry.AlgebraicSpace.etaleLocalOnTarget.iff_property_snd :
  ∀ {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    [P.RespectsIso] {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f),

    etaleLocalOnTarget P f ↔
      ∀ {V : Over S} (b : yoneda.obj V ⟶ Y.functorOfPoints),
        (over (@AlgebraicGeometry.Etale)).presheaf b → P (hf.snd b).left)

/- There is an étale morphism from a scheme to the target which is étale-locally
surjective, together with a represented pullback whose projection has property
`P`. -/
#check (AlgebraicGeometry.AlgebraicSpace.etaleLocalOnTarget.existsSurjectivePullback :
  ∀ {S : Scheme.{u}} (P : MorphismProperty Scheme.{u})
    {X Y : AlgebraicSpace S} (f : X ⟶ Y),
 Prop)

/- `existsSurjectivePullback P f` is the existence of a surjective étale scheme
pullback of `f` whose projection has property `P`. -/
#check (AlgebraicGeometry.AlgebraicSpace.etaleLocalOnTarget.existsSurjectivePullback_iff :
  ∀ {S : Scheme.{u}}
    {P : MorphismProperty Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),

    etaleLocalOnTarget.existsSurjectivePullback P f ↔
      ∃ (V W : Over S) (b : yoneda.obj V ⟶ Y.functorOfPoints)
        (fst : yoneda.obj W ⟶ X.functorOfPoints) (snd : W ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf b ∧
          Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) b ∧
            IsPullback fst (yoneda.map snd) f b ∧ P snd.left)

/- A surjective étale scheme pullback of `f` whose projection has property `P`
witnesses `existsSurjectivePullback P f`. -/
#check (AlgebraicGeometry.AlgebraicSpace.etaleLocalOnTarget.existsSurjectivePullback.of :
  ∀ {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} {V W : Over S}
    (b : yoneda.obj V ⟶ Y.functorOfPoints)
    (fst : yoneda.obj W ⟶ X.functorOfPoints) (snd : W ⟶ V)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (hs : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) b)
    (hpb : IsPullback fst (yoneda.map snd) f b) (hP : P snd.left),

    etaleLocalOnTarget.existsSurjectivePullback P f)

/- A morphism satisfying `existsSurjectivePullback P f` admits a surjective
étale scheme pullback whose projection has property `P`. -/
#check (AlgebraicGeometry.AlgebraicSpace.etaleLocalOnTarget.existsSurjectivePullback.spec :
  ∀ {S : Scheme.{u}} {P : MorphismProperty Scheme.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} (h : etaleLocalOnTarget.existsSurjectivePullback P f),

    ∃ (V W : Over S) (b : yoneda.obj V ⟶ Y.functorOfPoints)
      (fst : yoneda.obj W ⟶ X.functorOfPoints) (snd : W ⟶ V),
      (over (@AlgebraicGeometry.Etale)).presheaf b ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) b ∧
          IsPullback fst (yoneda.map snd) f b ∧ P snd.left)

/- If `X` and `Y` are representable, then some surjective étale scheme pullback
of the induced morphism of algebraic spaces has property `P` if and only if the
underlying scheme morphism has `P`. -/
#check (AlgebraicGeometry.AlgebraicSpace.etaleLocalOnTarget.existsSurjectivePullback_ofOverMap_iff :
  ∀ {S : Scheme.{u}}
    {P : MorphismProperty Scheme.{u}}
    [P.IsLocalAtTarget Scheme.etalePrecoverage] {U V : Over S} (h : U ⟶ V),

    etaleLocalOnTarget.existsSurjectivePullback P (ofOverMap h) ↔ P h.left)

end AlgebraicGeometry.AlgebraicSpace
