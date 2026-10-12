/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Morphism
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.Product

/-!
# Scheme-theoretic arrow images of groupoid-scheme morphisms

This module describes the canonical source, target, and composition maps associated to
the scheme-theoretic arrow image and the laws needed to make that image a groupoid scheme.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme.Hom

/-- The source map on the scheme-theoretic arrow image induced by the target groupoid. -/
noncomputable def imageSource {S : Scheme.{u}} {G₁ G₂ : GroupoidScheme S}
    (f : Hom G₁ G₂) : Scheme.Hom.imageOver f.arrow ⟶ G₂.U :=
  Scheme.Hom.imageιOver f.arrow ≫ G₂.s

/-- The target map on the scheme-theoretic arrow image induced by the target groupoid. -/
noncomputable def imageTarget {S : Scheme.{u}} {G₁ G₂ : GroupoidScheme S}
    (f : Hom G₁ G₂) : Scheme.Hom.imageOver f.arrow ⟶ G₂.U :=
  Scheme.Hom.imageιOver f.arrow ≫ G₂.t

/-- The target-groupoid composition on pairs of arrows in the scheme-theoretic image. -/
noncomputable def imageComposition {S : Scheme.{u}} {G₁ G₂ : GroupoidScheme S}
    (f : Hom G₁ G₂) :
    pullback (imageSource f) (imageTarget f) ⟶ G₂.R :=
  let i := Scheme.Hom.imageιOver f.arrow
  pullback.map (imageSource f) (imageTarget f) G₂.s G₂.t i i (𝟙 G₂.U)
    (Category.comp_id _) (Category.comp_id _) ≫ G₂.c

/-- Explicit operations on the scheme-theoretic arrow image satisfy the groupoid laws and
are compatible with the target groupoid structure. -/
structure IsImageGroupoid
    {S : Scheme.{u}} {G₁ G₂ : GroupoidScheme S} (f : Hom G₁ G₂)
    (c : pullback (imageSource f) (imageTarget f) ⟶ Scheme.Hom.imageOver f.arrow)
    (e : G₂.U ⟶ Scheme.Hom.imageOver f.arrow)
    (i : Scheme.Hom.imageOver f.arrow ⟶ Scheme.Hom.imageOver f.arrow) : Prop where
  /-- The image composition factors the target-groupoid composition. -/
  composition_eq : c ≫ Scheme.Hom.imageιOver f.arrow = imageComposition f
  /-- The image identity factors the target-groupoid identity. -/
  identity_eq : e ≫ Scheme.Hom.imageιOver f.arrow = G₂.e
  /-- The image inverse factors the target-groupoid inverse. -/
  inverse_eq :
    i ≫ Scheme.Hom.imageιOver f.arrow = Scheme.Hom.imageιOver f.arrow ≫ G₂.i
  /-- Composition on the image has the expected source. -/
  comp_source :
    c ≫ imageSource f = pullback.snd (imageSource f) (imageTarget f) ≫ imageSource f
  /-- Composition on the image has the expected target. -/
  comp_target :
    c ≫ imageTarget f = pullback.fst (imageSource f) (imageTarget f) ≫ imageTarget f
  /-- The identity on the image is a section of its source map. -/
  identity_source : e ≫ imageSource f = 𝟙 G₂.U
  /-- The identity on the image is a section of its target map. -/
  identity_target : e ≫ imageTarget f = 𝟙 G₂.U
  /-- Inversion on the image exchanges source with target. -/
  inverse_source : i ≫ imageSource f = imageTarget f
  /-- Inversion on the image exchanges target with source. -/
  inverse_target : i ≫ imageTarget f = imageSource f
  /-- Composition on the image is associative. -/
  associativity :
    ∀ {T : Over S} (a b d : T ⟶ Scheme.Hom.imageOver f.arrow)
      (h_ab : a ≫ imageSource f = b ≫ imageTarget f)
      (h_bd : b ≫ imageSource f = d ≫ imageTarget f)
      (h_ab_d : (pullback.lift a b h_ab ≫ c) ≫ imageSource f = d ≫ imageTarget f)
      (h_a_bd : a ≫ imageSource f = (pullback.lift b d h_bd ≫ c) ≫ imageTarget f),
      pullback.lift (pullback.lift a b h_ab ≫ c) d h_ab_d ≫ c =
        pullback.lift a (pullback.lift b d h_bd ≫ c) h_a_bd ≫ c
  /-- Right composition with the image identity fixes every image arrow. -/
  right_identity :
    ∀ {T : Over S} (a : T ⟶ Scheme.Hom.imageOver f.arrow)
      (h : a ≫ imageSource f = ((a ≫ imageSource f) ≫ e) ≫ imageTarget f),
      pullback.lift a ((a ≫ imageSource f) ≫ e) h ≫ c = a
  /-- Left composition with the image identity fixes every image arrow. -/
  left_identity :
    ∀ {T : Over S} (a : T ⟶ Scheme.Hom.imageOver f.arrow)
      (h : ((a ≫ imageTarget f) ≫ e) ≫ imageSource f = a ≫ imageTarget f),
      pullback.lift ((a ≫ imageTarget f) ≫ e) a h ≫ c = a
  /-- Composing an image arrow with its inverse gives the identity at its target. -/
  inverse_comp :
    ∀ {T : Over S} (a : T ⟶ Scheme.Hom.imageOver f.arrow)
      (h : a ≫ imageSource f = (a ≫ i) ≫ imageTarget f),
      pullback.lift a (a ≫ i) h ≫ c = (a ≫ imageTarget f) ≫ e
  /-- Composing the inverse of an image arrow with the arrow gives the identity at its source. -/
  comp_inverse :
    ∀ {T : Over S} (a : T ⟶ Scheme.Hom.imageOver f.arrow)
      (h : (a ≫ i) ≫ imageSource f = a ≫ imageTarget f),
      pullback.lift (a ≫ i) a h ≫ c = (a ≫ imageSource f) ≫ e

namespace IsImageGroupoid

/-- Bundle explicit image operations satisfying the groupoid laws into a groupoid scheme. -/
noncomputable def toGroupoidScheme
    {S : Scheme.{u}} {G₁ G₂ : GroupoidScheme S} {f : Hom G₁ G₂}
    {c : pullback (imageSource f) (imageTarget f) ⟶ Scheme.Hom.imageOver f.arrow}
    {e : G₂.U ⟶ Scheme.Hom.imageOver f.arrow}
    {i : Scheme.Hom.imageOver f.arrow ⟶ Scheme.Hom.imageOver f.arrow}
    (h : IsImageGroupoid f c e i) : GroupoidScheme S where
  U := G₂.U
  R := Scheme.Hom.imageOver f.arrow
  s := imageSource f
  t := imageTarget f
  c := c
  e := e
  i := i
  comp_source := h.comp_source
  comp_target := h.comp_target
  identity_source := h.identity_source
  identity_target := h.identity_target
  inverse_source := h.inverse_source
  inverse_target := h.inverse_target
  associativity := h.associativity
  right_identity := h.right_identity
  left_identity := h.left_identity
  inverse_comp := h.inverse_comp
  comp_inverse := h.comp_inverse

end IsImageGroupoid

/-- For an identity-on-objects morphism of groupoid schemes over a field whose arrow map
is quasi-compact, the scheme-theoretic arrow image admits compatible composition,
identity, and inverse operations satisfying the groupoid laws. -/
theorem image
    {S : Scheme.{u}} {k : Type u} [Field k] {G₁ G₂ : GroupoidScheme S}
    (eU : Spec (CommRingCat.of k) ≅ G₁.U.left) (hU : G₁.U = G₂.U)
    (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) [QuasiCompact f.arrow.left] :
    ∃ c : pullback (imageSource f) (imageTarget f) ⟶ Scheme.Hom.imageOver f.arrow,
      ∃ e : G₂.U ⟶ Scheme.Hom.imageOver f.arrow,
        ∃ i : Scheme.Hom.imageOver f.arrow ⟶ Scheme.Hom.imageOver f.arrow,
          IsImageGroupoid f c e i := sorry

end AlgebraicGeometry.GroupoidScheme.Hom
