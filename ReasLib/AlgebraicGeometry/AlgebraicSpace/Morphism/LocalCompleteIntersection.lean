/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleFromScheme
import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection.Composition
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.LocalCompleteIntersection
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Smooth

/-!
# Local complete intersection morphisms of algebraic spaces

Local complete intersection morphisms of algebraic spaces are tested on étale
scheme squares.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X ⟶ Y` of algebraic spaces over `S` is a local complete
intersection morphism when every commutative square with étale vertical arrows
from schemes has local-complete-intersection top arrow. -/
class IsLocalCompleteIntersection {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- Every étale scheme square over `f` has local-complete-intersection top
  arrow. -/
  of_etale {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
      (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
      (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
      (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
      (w : a ≫ f = yoneda.map h ≫ b) :
    AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection h.left

/-- A morphism of algebraic spaces is a local complete intersection exactly
when every étale scheme square over it has local-complete-intersection top
arrow. -/
theorem isLocalCompleteIntersection_iff {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    IsLocalCompleteIntersection f ↔
      ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
        (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf a →
          (over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = yoneda.map h ≫ b →
              AlgebraicGeometry.LocallyOfType
                RingHom.IsLocalCompleteIntersection h.left :=
  ⟨fun hf => hf.of_etale, fun hf => ⟨hf⟩⟩

namespace IsLocalCompleteIntersection

/-- An étale scheme square over a local complete intersection morphism of
algebraic spaces has local-complete-intersection top arrow. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsLocalCompleteIntersection f] {U V : Over S}
    (a : yoneda.obj U ⟶ X.functorOfPoints)
    (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
    (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = yoneda.map h ≫ b) :
    AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection h.left :=
  of_etale a b h ha hb w

/-- The identity morphism of an algebraic space is a local complete
intersection. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    IsLocalCompleteIntersection (𝟙 X) := by
  refine ⟨fun a b h ha hb w => ?_⟩
  haveI : AlgebraicGeometry.Etale h.left :=
    etale_of_comp a b h ha hb (by
      change a ≫ 𝟙 X.functorOfPoints = _ at w
      simpa only [Category.comp_id] using w)
  exact ((AlgebraicGeometry.Syntomic.iff_flat_and_isLocalCompleteIntersection h.left).mp
    inferInstance).2

/-- A representable morphism of algebraic spaces with the relative
local-complete-intersection property is a local complete intersection. -/
theorem of_presheaf {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : (over
        (@AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection :
          MorphismProperty Scheme.{u})).presheaf f) :
    IsLocalCompleteIntersection f := by
  refine ⟨fun a b h ha hb w => ?_⟩
  -- The represented pullback of `f` along `b` is étale over `X`.
  have hc : (over (@AlgebraicGeometry.Etale)).presheaf (hf.rep.fst b) :=
    (relative_isStableUnderBaseChange (over (@AlgebraicGeometry.Etale))
      (F := yoneda)).of_isPullback (hf.rep.isPullback b).flip hb
  haveI : AlgebraicGeometry.Etale (hf.rep.lift a h w).left :=
    etale_of_comp a (hf.rep.fst b) (hf.rep.lift a h w) ha hc
      (hf.rep.lift_fst a h w).symm
  haveI : AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection
      (hf.rep.lift a h w).left :=
    ((AlgebraicGeometry.Syntomic.iff_flat_and_isLocalCompleteIntersection _).mp
      inferInstance).2
  haveI : AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection
      (hf.rep.snd b).left := hf.property_snd b
  -- The scheme map factors through this pullback by an étale morphism.
  rw [← hf.rep.lift_snd a h w]
  exact AlgebraicGeometry.LocallyOfType.isLocalCompleteIntersection_comp _ _

end IsLocalCompleteIntersection

/-- A morphism `f : X ⟶ Y` of algebraic spaces is Koszul at a point `x` of `X`
if it is a local complete intersection after restriction to some open subspace
neighbourhood of `x`. -/
def KoszulAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) : Prop :=
  ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
    IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧
      IsLocalCompleteIntersection (i ≫ f)

/-- Koszulness at a point is the existence of an open subspace neighbourhood on
which the morphism is a local complete intersection. -/
theorem koszulAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) :
    KoszulAt f x ↔
      ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
        IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧
          IsLocalCompleteIntersection (i ≫ f) :=
  Iff.rfl

namespace KoszulAt

/-- An open immersion `i : X' ⟶ X` whose composite `i ≫ f` is a local complete
intersection witnesses that `f` is Koszul at every point of the image of
`|X'|`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {x : Points X} {X' : AlgebraicSpace S} {i : X' ⟶ X}
    [IsOpenImmersion i] (hx : x ∈ Set.range (Points.map i))
    [IsLocalCompleteIntersection (i ≫ f)] : KoszulAt f x :=
  ⟨X', i, inferInstance, hx, inferInstance⟩

end KoszulAt

/-- A local complete intersection morphism of algebraic spaces is Koszul at
every point of its source. -/
theorem koszulAt_of_isLocalCompleteIntersection {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsLocalCompleteIntersection f]
    (x : Points X) : KoszulAt f x := by
  refine ⟨X, 𝟙 X, ?_, ?_, ?_⟩
  · refine ⟨?_⟩
    change (over (@AlgebraicGeometry.IsOpenImmersion)).presheaf (𝟙 X.functorOfPoints)
    refine ⟨Functor.relativelyRepresentable.of_isIso yoneda _, ?_⟩
    intro U V g fst snd sq
    have : IsIso (yoneda.map snd) := sq.isIso_snd_of_isIso
    have : IsIso snd := isIso_of_reflects_iso snd yoneda
    have : IsIso snd.left := inferInstanceAs (IsIso ((Over.forget S).map snd))
    change AlgebraicGeometry.IsOpenImmersion snd.left
    infer_instance
  · refine ⟨x, ?_⟩
    exact Quotient.inductionOn x (fun _ => rfl)
  · simpa only [Category.id_comp] using (inferInstance : IsLocalCompleteIntersection f)

end AlgebraicGeometry.AlgebraicSpace
