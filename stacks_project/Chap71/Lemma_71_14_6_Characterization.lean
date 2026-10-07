module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap71.Lemma_71_14_3_RelativelyAmple

/-!
# Scheme, affine, and étale characterizations of relative ampleness

Relative ampleness of an invertible module on a morphism of algebraic spaces is
tested after every scheme base change, after every affine scheme base change, or
after some surjective étale scheme base change.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace RelativelyAmple

/-- After every morphism from a scheme, the fibre product is a scheme and the
pulled-back module is relatively ample over that scheme. -/
def forallScheme {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (L : X.Modules) : Prop :=
  ∀ (Z : Over S) (g : ofOver Z ⟶ Y),
    IsScheme (pullback f g) ∧
      RelativelyAmple (pullback.snd f g)
        ((Modules.pullback (pullback.fst f g)).obj L)

/-- `forallScheme f L` is the condition that every scheme base change of `f`
has scheme source and relatively ample pullback of `L`. -/
theorem forallScheme_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (L : X.Modules) :
    forallScheme f L ↔
      ∀ (Z : Over S) (g : ofOver Z ⟶ Y),
        IsScheme (pullback f g) ∧
          RelativelyAmple (pullback.snd f g)
            ((Modules.pullback (pullback.fst f g)).obj L) :=
  sorry

namespace forallScheme

/-- The universal scheme-base-change condition witnesses `forallScheme f L`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {L : X.Modules}
    (h : ∀ (Z : Over S) (g : ofOver Z ⟶ Y),
      IsScheme (pullback f g) ∧
        RelativelyAmple (pullback.snd f g)
          ((Modules.pullback (pullback.fst f g)).obj L)) :
    forallScheme f L :=
  sorry

/-- Under `forallScheme f L`, every scheme base change of `f` is a scheme and
the pulled-back module is relatively ample. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {L : X.Modules} (h : forallScheme f L) :
    ∀ (Z : Over S) (g : ofOver Z ⟶ Y),
      IsScheme (pullback f g) ∧
        RelativelyAmple (pullback.snd f g)
          ((Modules.pullback (pullback.fst f g)).obj L) :=
  sorry

end forallScheme

/-- After every morphism from an affine scheme, the fibre product is a scheme
and the pulled-back module is relatively ample over that affine scheme. -/
def forallAffine {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (L : X.Modules) : Prop :=
  ∀ (Z : Over S) [AlgebraicGeometry.IsAffine Z.left] (g : ofOver Z ⟶ Y),
    IsScheme (pullback f g) ∧
      RelativelyAmple (pullback.snd f g)
        ((Modules.pullback (pullback.fst f g)).obj L)

/-- `forallAffine f L` is the condition that every affine scheme base change of
`f` has scheme source and relatively ample pullback of `L`. -/
theorem forallAffine_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (L : X.Modules) :
    forallAffine f L ↔
      ∀ (Z : Over S) [AlgebraicGeometry.IsAffine Z.left] (g : ofOver Z ⟶ Y),
        IsScheme (pullback f g) ∧
          RelativelyAmple (pullback.snd f g)
            ((Modules.pullback (pullback.fst f g)).obj L) :=
  sorry

namespace forallAffine

/-- The universal affine-scheme-base-change condition witnesses
`forallAffine f L`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {L : X.Modules}
    (h : ∀ (Z : Over S) [AlgebraicGeometry.IsAffine Z.left] (g : ofOver Z ⟶ Y),
      IsScheme (pullback f g) ∧
        RelativelyAmple (pullback.snd f g)
          ((Modules.pullback (pullback.fst f g)).obj L)) :
    forallAffine f L :=
  sorry

/-- Under `forallAffine f L`, every affine scheme base change of `f` is a scheme
and the pulled-back module is relatively ample. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {L : X.Modules} (h : forallAffine f L) :
    ∀ (Z : Over S) [AlgebraicGeometry.IsAffine Z.left] (g : ofOver Z ⟶ Y),
      IsScheme (pullback f g) ∧
        RelativelyAmple (pullback.snd f g)
          ((Modules.pullback (pullback.fst f g)).obj L) :=
  sorry

end forallAffine

/-- There is a scheme and a surjective étale morphism to the target such that the
fibre product is a scheme and the pulled-back module is relatively ample. -/
def existsSurjectiveEtale {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (L : X.Modules) : Prop :=
  ∃ (V : Over S) (h : ofOver V ⟶ Y),
    Etale h ∧ Surjective h ∧ IsScheme (pullback f h) ∧
      RelativelyAmple (pullback.snd f h)
        ((Modules.pullback (pullback.fst f h)).obj L)

/-- `existsSurjectiveEtale f L` is the existence of a surjective étale scheme
atlas of the target along which the fibre product is a scheme and the pullback
of `L` is relatively ample. -/
theorem existsSurjectiveEtale_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (L : X.Modules) :
    existsSurjectiveEtale f L ↔
      ∃ (V : Over S) (h : ofOver V ⟶ Y),
        Etale h ∧ Surjective h ∧ IsScheme (pullback f h) ∧
          RelativelyAmple (pullback.snd f h)
            ((Modules.pullback (pullback.fst f h)).obj L) :=
  sorry

namespace existsSurjectiveEtale

/-- A surjective étale scheme morphism along which the fibre product is a scheme
and the pulled-back module is relatively ample witnesses
`existsSurjectiveEtale f L`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {L : X.Modules}
    {V : Over S} (h : ofOver V ⟶ Y) [Etale h] [Surjective h]
    (h_scheme : IsScheme (pullback f h))
    (h_ample : RelativelyAmple (pullback.snd f h)
      ((Modules.pullback (pullback.fst f h)).obj L)) :
    existsSurjectiveEtale f L :=
  sorry

/-- `existsSurjectiveEtale f L` supplies a surjective étale scheme morphism
along which the fibre product is a scheme and the pulled-back module is
relatively ample. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {L : X.Modules} (h : existsSurjectiveEtale f L) :
    ∃ (V : Over S) (h : ofOver V ⟶ Y),
      Etale h ∧ Surjective h ∧ IsScheme (pullback f h) ∧
        RelativelyAmple (pullback.snd f h)
          ((Modules.pullback (pullback.fst f h)).obj L) :=
  sorry

end existsSurjectiveEtale

end RelativelyAmple

end AlgebraicGeometry.AlgebraicSpace
