/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_21_2_QuasiAffine
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Definition_67_48_3_Normalization
public import stacks_project.Chap67.Lemma_67_27_3_QuasiFinite

/-!
# Zariski's Main Theorem for quasi-finite separated morphisms

A quasi-finite separated morphism of algebraic spaces factors through its
relative normalization as a quasi-compact open immersion followed by an
integral morphism, and is therefore quasi-affine.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- Lemma 67.52.2 (1): let `S` be a scheme, and let `f : X ⟶ Y` be a quasi-finite
separated morphism of algebraic spaces over `S`. Let `Y'` be the normalization of
`Y` in `X`, with the canonical factorization
`toNormalization f ≫ fromNormalization f = f`. Then `toNormalization f` is an
open immersion. -/
@[stacks 0ABS]
instance instIsOpenImmersionToNormalization
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiFinite f] [Separated f] :
    IsOpenImmersion (toNormalization f) :=
  sorry

/-- Lemma 67.52.2 (2): let `S` be a scheme, and let `f : X ⟶ Y` be a quasi-finite
separated morphism of algebraic spaces over `S`. With the canonical factorization
`toNormalization f ≫ fromNormalization f = f`, the morphism `toNormalization f`
is quasi-compact, and is therefore a quasi-compact open immersion. -/
@[stacks 0ABS]
instance instQuasiCompactToNormalization
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiFinite f] [Separated f] :
    QuasiCompact (toNormalization f) :=
  sorry

/-- Lemma 67.52.2 (3): let `S` be a scheme, and let `f : X ⟶ Y` be a quasi-finite
separated morphism of algebraic spaces over `S`. With the canonical factorization
`toNormalization f ≫ fromNormalization f = f`, the morphism
`fromNormalization f` is integral. -/
@[stacks 0ABS]
instance instIsIntegralHomFromNormalization
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiFinite f] [Separated f] :
    IsIntegralHom (fromNormalization f) :=
  sorry

end Hom

namespace QuasiFinite

/-- Lemma 67.52.2 (4): let `S` be a scheme, and let `f : X ⟶ Y` be a quasi-finite
separated morphism of algebraic spaces over `S`. In particular `f` is
quasi-affine. -/
@[stacks 0ABS]
instance instQuasiAffine {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiFinite f] [Separated f] : QuasiAffine f :=
  sorry

end QuasiFinite

end AlgebraicGeometry.AlgebraicSpace
