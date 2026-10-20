module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Unramified
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids.Hom
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Flat
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFinitePresentation
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic

/-!
# Characterizations of unramified morphisms of algebraic stacks

Unramifiedness is equivalent to the DM condition together with unramifiedness
of every étale algebraic-space comparison on arbitrary algebraic-space
pullbacks, and to the existence of an unramified comparison on one fppf
algebraic-space cover of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Unramified

/-- For every algebraic space `V` and morphism `g : V.toGroupoids ⟶ Y`, every
étale morphism from an algebraic space into `TwoFibreProduct.apex f g`
(informally `X ×_Y V`) recovers an unramified morphism of algebraic spaces
to `V`. -/
def forallEtaleOnPullbacks {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop :=
  ∀ (V : AlgebraicSpace S) (g : V.toGroupoids ⟶ Y) (U : AlgebraicSpace S)
    (p : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g),
    Groupoids.Hom.Etale p → AlgebraicSpace.Unramified (AlgebraicSpace.toGroupoids.eval
      (p ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))

/-- `forallEtaleOnPullbacks f` unpacks to unramifiedness of the recovered
morphism of algebraic spaces for every étale algebraic-space comparison into
a 2-fibre product of `f` against an algebraic space over the target. -/
theorem forallEtaleOnPullbacks.iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    forallEtaleOnPullbacks f ↔
      ∀ (V : AlgebraicSpace S) (g : V.toGroupoids ⟶ Y) (U : AlgebraicSpace S)
        (p : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g),
        Groupoids.Hom.Etale p → AlgebraicSpace.Unramified (AlgebraicSpace.toGroupoids.eval
          (p ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)) :=
  Iff.rfl

namespace forallEtaleOnPullbacks

/-- Unramifiedness of every recovered étale algebraic-space comparison into a
2-fibre product of `f` against an algebraic space over the target witnesses
`forallEtaleOnPullbacks`. -/
theorem of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (h : ∀ (V : AlgebraicSpace S) (g : V.toGroupoids ⟶ Y)
      (U : AlgebraicSpace S)
      (p : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g),
      Groupoids.Hom.Etale p → AlgebraicSpace.Unramified (AlgebraicSpace.toGroupoids.eval
        (p ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))) :
    forallEtaleOnPullbacks f :=
  h

/-- Under `forallEtaleOnPullbacks f`, an étale algebraic-space comparison into
a 2-fibre product of `f` against an algebraic space over the target recovers
an unramified morphism of algebraic spaces. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : forallEtaleOnPullbacks f) (V : AlgebraicSpace S)
    (g : V.toGroupoids ⟶ Y) (U : AlgebraicSpace S)
    (p : U.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)
    (hp : Groupoids.Hom.Etale p) :
    AlgebraicSpace.Unramified (AlgebraicSpace.toGroupoids.eval
      (p ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)) :=
  hf V g U p hp

end forallEtaleOnPullbacks

/-- There exist algebraic spaces `W`, `T`, a surjective, flat, locally of
finite presentation morphism `g : W.toGroupoids ⟶ Y`, and a surjective étale
morphism `p` from `T` to `TwoFibreProduct.apex f g` (informally `X ×_Y W`)
such that the recovered morphism of algebraic spaces `T ⟶ W` is unramified. -/
def existsFppfEtaleSquare {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop :=
  ∃ (W T : AlgebraicSpace S) (g : W.toGroupoids ⟶ Y)
    (p : T.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g),
    Groupoids.Hom.Surjective g ∧ Groupoids.Hom.Flat g ∧
      Groupoids.Hom.LocallyOfFinitePresentation g ∧
      Groupoids.Hom.Surjective p ∧ Groupoids.Hom.Etale p ∧
      AlgebraicSpace.Unramified (AlgebraicSpace.toGroupoids.eval
        (p ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))

/-- `existsFppfEtaleSquare f` unpacks to one fppf algebraic-space cover of the
target together with a surjective étale algebraic-space comparison into the
2-fibre product whose recovered morphism of algebraic spaces is unramified. -/
theorem existsFppfEtaleSquare.iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    existsFppfEtaleSquare f ↔
      ∃ (W T : AlgebraicSpace S) (g : W.toGroupoids ⟶ Y)
        (p : T.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g),
        Groupoids.Hom.Surjective g ∧ Groupoids.Hom.Flat g ∧
          Groupoids.Hom.LocallyOfFinitePresentation g ∧
          Groupoids.Hom.Surjective p ∧ Groupoids.Hom.Etale p ∧
          AlgebraicSpace.Unramified (AlgebraicSpace.toGroupoids.eval
            (p ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)) :=
  Iff.rfl

namespace existsFppfEtaleSquare

/-- An fppf algebraic-space cover of the target together with a surjective
étale algebraic-space comparison into the 2-fibre product whose recovered
morphism of algebraic spaces is unramified witnesses `existsFppfEtaleSquare`. -/
theorem of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    {W T : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    (p : T.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)
    (h_surjective : Groupoids.Hom.Surjective g)
    (h_flat : Groupoids.Hom.Flat g)
    (h_locallyOfFinitePresentation : Groupoids.Hom.LocallyOfFinitePresentation g)
    (h_p_surjective : Groupoids.Hom.Surjective p)
    (h_p_etale : Groupoids.Hom.Etale p)
    (h_unramified : AlgebraicSpace.Unramified (AlgebraicSpace.toGroupoids.eval
      (p ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))) :
    existsFppfEtaleSquare f :=
  ⟨W, T, g, p, h_surjective, h_flat, h_locallyOfFinitePresentation,
    h_p_surjective, h_p_etale, h_unramified⟩

/-- `existsFppfEtaleSquare f` supplies an fppf algebraic-space cover of the
target and a surjective étale algebraic-space comparison into the 2-fibre
product whose recovered morphism of algebraic spaces is unramified. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : existsFppfEtaleSquare f) :
    ∃ (W T : AlgebraicSpace S) (g : W.toGroupoids ⟶ Y)
      (p : T.toGroupoids ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g),
      Groupoids.Hom.Surjective g ∧ Groupoids.Hom.Flat g ∧
        Groupoids.Hom.LocallyOfFinitePresentation g ∧
        Groupoids.Hom.Surjective p ∧ Groupoids.Hom.Etale p ∧
        AlgebraicSpace.Unramified (AlgebraicSpace.toGroupoids.eval
          (p ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)) :=
  hf

end existsFppfEtaleSquare

/-- Let `f : X ⟶ Y` be a morphism of algebraic stacks. The
following are equivalent: `f` is unramified; `f` is DM and for every algebraic
space `V` with `g : V.toGroupoids ⟶ Y` and every étale morphism from an
algebraic space into `TwoFibreProduct.apex f g`, the recovered morphism of
algebraic spaces is unramified; there exist a surjective, flat, locally of
finite presentation morphism from an algebraic space `W` to `Y` and a
surjective étale morphism from an algebraic space `T` to
`TwoFibreProduct.apex f g` such that the recovered morphism `T ⟶ W` is
unramified. -/
@[stacks 0CIY]
theorem tfae {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    List.TFAE
      [Unramified f, DM f ∧ forallEtaleOnPullbacks f, existsFppfEtaleSquare f] :=
  sorry

/-- A morphism of algebraic stacks is unramified if and only if it is DM and
every étale algebraic-space comparison into a 2-fibre product against an
algebraic space over the target recovers an unramified morphism. -/
theorem iff_forallEtaleOnPullbacks {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Unramified f ↔ DM f ∧ forallEtaleOnPullbacks f :=
  (tfae f).out 0 1

/-- A morphism of algebraic stacks is unramified if and only if some fppf
algebraic-space cover of the target has a surjective étale algebraic-space
comparison into the 2-fibre product whose recovered morphism is unramified. -/
theorem iff_existsFppfEtaleSquare {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    Unramified f ↔ existsFppfEtaleSquare f :=
  (tfae f).out 0 2

/-- An unramified morphism of algebraic stacks has unramified recovered
morphisms for every étale algebraic-space comparison into a 2-fibre product
against an algebraic space over the target. -/
theorem forallEtaleOnPullbacks_of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Unramified f] :
    forallEtaleOnPullbacks f :=
  ((iff_forallEtaleOnPullbacks f).mp inferInstance).2

/-- If a morphism of algebraic stacks is DM and every étale algebraic-space
comparison into a 2-fibre product against an algebraic space over the target
recovers an unramified morphism, then the morphism is unramified. -/
theorem of_forallEtaleOnPullbacks {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (hDM : DM f)
    (h : forallEtaleOnPullbacks f) : Unramified f :=
  (iff_forallEtaleOnPullbacks f).mpr ⟨hDM, h⟩

/-- An unramified morphism of algebraic stacks admits an fppf algebraic-space
cover of the target together with a surjective étale algebraic-space
comparison into the 2-fibre product whose recovered morphism is unramified. -/
theorem existsFppfEtaleSquare_of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Unramified f] :
    existsFppfEtaleSquare f :=
  (iff_existsFppfEtaleSquare f).mp inferInstance

/-- An fppf algebraic-space cover of the target together with a surjective
étale algebraic-space comparison into the 2-fibre product whose recovered
morphism is unramified implies that a morphism of algebraic stacks is
unramified. -/
theorem of_existsFppfEtaleSquare {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (h : existsFppfEtaleSquare f) : Unramified f :=
  (iff_existsFppfEtaleSquare f).mpr h

end AlgebraicGeometry.AlgebraicStack.Unramified
