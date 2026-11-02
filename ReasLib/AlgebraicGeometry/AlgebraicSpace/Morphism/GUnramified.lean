/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points

/-!
# G-unramified morphisms of algebraic spaces

A morphism of algebraic spaces is G-unramified when every étale scheme square
over it has G-unramified top arrow. Pointwise G-unramifiedness is
G-unramifiedness after restriction to an open subspace neighbourhood.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

private theorem etale_of_presheaf_triangle {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {U V : Over S}
    (a : yoneda.obj U ⟶ F) (b : yoneda.obj V ⟶ F) (h : U ⟶ V)
    (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a = yoneda.map h ≫ b) : AlgebraicGeometry.Etale h.left := by
  let l := hb.rep.lift' h (𝟙 U) (by simpa using w.symm)
  have hl_snd : l ≫ hb.rep.snd a = 𝟙 U := hb.rep.lift'_snd _ _ _
  have hl_fst : l ≫ hb.rep.fst' a = h := hb.rep.lift'_fst _ _ _
  haveI : AlgebraicGeometry.Etale (hb.rep.snd a).left := hb.property_snd a
  haveI : AlgebraicGeometry.Etale (hb.rep.fst' a).left :=
    ha.property b (yoneda.map (hb.rep.snd a)) (hb.rep.fst' a)
      (hb.rep.isPullback' a).flip
  haveI : AlgebraicGeometry.Etale (l.left ≫ (hb.rep.snd a).left) := by
    change AlgebraicGeometry.Etale (l ≫ hb.rep.snd a).left
    rw [hl_snd]
    change AlgebraicGeometry.Etale (𝟙 U.left)
    infer_instance
  haveI : AlgebraicGeometry.Etale l.left :=
    MorphismProperty.of_postcomp (@AlgebraicGeometry.Etale)
      (W' := @AlgebraicGeometry.Etale) l.left (hb.rep.snd a).left
        inferInstance inferInstance
  have hh : h.left = l.left ≫ (hb.rep.fst' a).left :=
    congrArg (fun k : U ⟶ V ↦ k.left) hl_fst.symm
  rw [hh]
  infer_instance

/-- A morphism `f : X ⟶ Y` of algebraic spaces over `S` is G-unramified if
every commutative square with étale vertical arrows from schemes has
G-unramified top arrow. -/
class GUnramified {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- Every étale scheme square over `f` has G-unramified top arrow. -/
  of_etale {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
      (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
      (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
      (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
      (w : a ≫ f = yoneda.map h ≫ b) :
    AlgebraicGeometry.GUnramified h.left

/-- A morphism of algebraic spaces is G-unramified if and only if every
commutative square with étale vertical arrows from schemes has G-unramified
top arrow. -/
theorem gUnramified_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    GUnramified f ↔
      ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
        (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf a →
          (over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = yoneda.map h ≫ b → AlgebraicGeometry.GUnramified h.left :=
  ⟨fun hf ↦ hf.of_etale, fun hf ↦ ⟨hf⟩⟩

namespace GUnramified

/-- An étale scheme square over a G-unramified morphism of algebraic spaces has
G-unramified top arrow. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [GUnramified f] {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
    (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
    (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = yoneda.map h ≫ b) : AlgebraicGeometry.GUnramified h.left :=
  GUnramified.of_etale a b h ha hb w

/-- The identity morphism of an algebraic space is G-unramified. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : GUnramified (𝟙 X) := by
  constructor
  intro U V a b h ha hb w
  have he : AlgebraicGeometry.Etale h.left :=
    etale_of_presheaf_triangle a b h ha hb (by
      change a ≫ (𝟙 X.functorOfPoints) = yoneda.map h ≫ b at w
      simpa only [Category.comp_id] using w)
  have he' := AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified.mp he
  exact
    { toFormallyUnramified := he'.2.1
      toLocallyOfFinitePresentation := he'.2.2 }

/-- A representable morphism of algebraic spaces with the relative G-unramified
property is G-unramified. -/
theorem of_presheaf {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : (over
        (@AlgebraicGeometry.GUnramified :
          MorphismProperty Scheme.{u})).presheaf f) :
    GUnramified f := by
  constructor
  intro U V a b h ha hb w
  let l := hf.rep.lift a h w
  have hl : yoneda.map l ≫ hf.rep.fst b = a := hf.rep.lift_fst a h w
  have hfst : (over (@AlgebraicGeometry.Etale)).presheaf (hf.rep.fst b) :=
    (MorphismProperty.relative_isStableUnderBaseChange
      (over (@AlgebraicGeometry.Etale)) (F := yoneda)).of_isPullback
        (hf.rep.isPullback b).flip hb
  have he := AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified.mp
    (etale_of_presheaf_triangle a (hf.rep.fst b) l ha hfst hl.symm)
  have hg : AlgebraicGeometry.GUnramified (hf.rep.snd b).left := hf.property_snd b
  have hh : h.left = l.left ≫ (hf.rep.snd b).left :=
    congrArg (fun k : U ⟶ V ↦ k.left) (hf.rep.lift_snd a h w).symm
  rw [hh]
  exact
    { toFormallyUnramified := MorphismProperty.comp_mem
        (@AlgebraicGeometry.FormallyUnramified) _ _ he.2.1 hg.toFormallyUnramified
      toLocallyOfFinitePresentation := MorphismProperty.comp_mem
        (@AlgebraicGeometry.LocallyOfFinitePresentation) _ _
          he.2.2 hg.toLocallyOfFinitePresentation }

end GUnramified

/-- A G-unramified morphism of algebraic spaces is unramified. -/
instance unramified_of_gUnramified {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [GUnramified f] : Unramified f := by
  constructor
  intro U V a b h ha hb w
  have hg : AlgebraicGeometry.GUnramified h.left := GUnramified.of_etale a b h ha hb w
  letI : AlgebraicGeometry.LocallyOfFinitePresentation h.left := hg.toLocallyOfFinitePresentation
  exact
    { toFormallyUnramified := hg.toFormallyUnramified
      toLocallyOfFiniteType := ⟨fun {_} hU {_} hV e ↦ RingHom.FiniteType.of_finitePresentation
        (h.left.finitePresentation_appLE hU hV e)⟩ }

/-- A morphism `f : X ⟶ Y` of algebraic spaces is G-unramified at a point `x`
of `X` if it is G-unramified after restriction to some open subspace
neighbourhood of `x`. -/
def GUnramifiedAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) : Prop :=
  ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
    IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧ GUnramified (i ≫ f)

/-- G-unramifiedness at a point is the existence of an open subspace
neighbourhood on which the morphism is G-unramified. -/
theorem gUnramifiedAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) :
    GUnramifiedAt f x ↔
      ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
        IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧ GUnramified (i ≫ f) :=
  Iff.rfl

namespace GUnramifiedAt

/-- An open immersion `i : X' ⟶ X` whose composite `i ≫ f` is G-unramified
witnesses that `f` is G-unramified at every point of the image of `|X'|`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {x : Points X} {X' : AlgebraicSpace S} {i : X' ⟶ X}
    [IsOpenImmersion i] (hx : x ∈ Set.range (Points.map i))
    [GUnramified (i ≫ f)] : GUnramifiedAt f x :=
  ⟨X', i, inferInstance, hx, inferInstance⟩

end GUnramifiedAt

/-- A G-unramified morphism of algebraic spaces is G-unramified at every point
of its source. -/
theorem gUnramifiedAt_of_gUnramified {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [GUnramified f] (x : Points X) : GUnramifiedAt f x := by
  have hi : IsOpenImmersion (𝟙 X) := by
    constructor
    change (over (@AlgebraicGeometry.IsOpenImmersion)).presheaf (𝟙 X.functorOfPoints)
    refine ⟨Functor.relativelyRepresentable.of_isIso yoneda _, ?_⟩
    intro U V b a h hp
    haveI : IsIso (yoneda.map h) := hp.isIso_snd_of_isIso
    haveI : IsIso h := isIso_of_reflects_iso h yoneda
    haveI : IsIso h.left := inferInstanceAs (IsIso ((Over.forget S).map h))
    change AlgebraicGeometry.IsOpenImmersion h.left
    infer_instance
  refine ⟨X, 𝟙 X, hi, ?_, ?_⟩
  · refine ⟨x, ?_⟩
    refine Quotient.inductionOn x (fun p ↦ ?_)
    rfl
  · simpa using (inferInstance : GUnramified f)

end AlgebraicGeometry.AlgebraicSpace
