module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap71.Lemma_71_14_6_Characterization

/-!
# Lemma 71.14.6

Relative ampleness of an invertible module on a morphism of algebraic spaces is
equivalent to the same condition after every scheme base change, after every
affine scheme base change, and after some surjective étale scheme base change.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory Limits MonoidalCategory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace RelativelyAmple

/-- Lemma 71.14.6: let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Let `L` be an invertible `𝒪_X`-module. The following
are equivalent: `RelativelyAmple f L`; for every scheme `Z` over `S` and every
morphism `g : ofOver Z ⟶ Y`, the algebraic space `pullback f g` is a scheme and
the pullback of `L` is relatively ample over `Z`; the same for every affine
scheme `Z`; and there exists a scheme `V` and a surjective étale morphism
`h : ofOver V ⟶ Y` such that `pullback f h` is a scheme and the pullback of `L`
is relatively ample over `V`. -/
@[stacks 0D36]
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
  sorry

/-- Relative ampleness of an invertible module is equivalent to the same
condition after every affine scheme base change. -/
theorem iff_forallAffine {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (L : X.Modules) [isInvertibleObject L] :
    RelativelyAmple f L ↔ forallAffine f L :=
  sorry

/-- Relative ampleness of an invertible module is equivalent to the existence of
a surjective étale scheme atlas of the target along which the fibre product is a
scheme and the pulled-back module is relatively ample. -/
theorem iff_existsSurjectiveEtale {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (L : X.Modules) [isInvertibleObject L] :
    RelativelyAmple f L ↔ existsSurjectiveEtale f L :=
  sorry

end RelativelyAmple

end AlgebraicGeometry.AlgebraicSpace
