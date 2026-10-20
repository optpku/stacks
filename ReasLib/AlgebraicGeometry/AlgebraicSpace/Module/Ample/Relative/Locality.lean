module

public import Mathlib.Data.List.TFAE
public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ample.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal

/-!
# Locality of relative ampleness on algebraic spaces

Relative ampleness of an invertible module can be tested after every scheme base
change, every affine scheme base change, or some surjective étale scheme base change.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory Limits MonoidalCategory

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
  by rfl

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
  by rfl

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
  by rfl

/-- Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Let `L` be an invertible `𝒪_X`-module. The following
are equivalent: `RelativelyAmple f L`; for every scheme `Z` over `S` and every
morphism `g : ofOver Z ⟶ Y`, the algebraic space `pullback f g` is a scheme and
the pullback of `L` is relatively ample over `Z`; the same for every affine
scheme `Z`; and there exists a scheme `V` and a surjective étale morphism
`h : ofOver V ⟶ Y` such that `pullback f h` is a scheme and the pullback of `L`
is relatively ample over `V`. -/
theorem tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (L : X.Modules) [isInvertibleObject L] :
    List.TFAE [RelativelyAmple f L, forallScheme f L, forallAffine f L,
      existsSurjectiveEtale f L] :=
  sorry

/-- Relative ampleness of an invertible module is equivalent to the same
condition after every scheme base change. -/
theorem iff_forallScheme {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (L : X.Modules) [isInvertibleObject L] :
    RelativelyAmple f L ↔ forallScheme f L :=
  (tfae f L).out 0 1

/-- Relative ampleness of an invertible module is equivalent to the same
condition after every affine scheme base change. -/
theorem iff_forallAffine {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (L : X.Modules) [isInvertibleObject L] :
    RelativelyAmple f L ↔ forallAffine f L :=
  (tfae f L).out 0 2

/-- Relative ampleness of an invertible module is equivalent to the existence of
a surjective étale scheme atlas of the target along which the fibre product is a
scheme and the pulled-back module is relatively ample. -/
theorem iff_existsSurjectiveEtale {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (L : X.Modules) [isInvertibleObject L] :
    RelativelyAmple f L ↔ existsSurjectiveEtale f L :=
  (tfae f L).out 0 3

end RelativelyAmple

end AlgebraicGeometry.AlgebraicSpace
