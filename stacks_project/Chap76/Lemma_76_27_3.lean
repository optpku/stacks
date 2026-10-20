/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.RingHom.Flat
public import stacks_project.Chap71.Lemma_71_4_6_Fiber
public import stacks_project.Chap76.Lemma_76_27_3_Fiber
public import stacks_project.Chap76.Lemma_76_27_3_Gorenstein

/-!
# Characterizations of Gorenstein morphisms of algebraic spaces

For a morphism of algebraic spaces with locally Noetherian fibres, Gorensteinness
is equivalent to flatness together with Gorenstein residue-field fibres after
some, equivalently any, étale morphism from a scheme to the target. Pointwise,
Gorensteinness is equivalent to flatness of the induced map of étale local rings
together with Gorensteinness of the closed fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.27.3 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume the fibres of `f` are locally Noetherian.
The following are equivalent: `f` is Gorenstein; `f` is flat and for some
surjective étale morphism `V ⟶ Y` where `V` is a scheme, the fibres of
`X_V ⟶ V` are Gorenstein algebraic spaces; and `f` is flat and for any étale
morphism `V ⟶ Y` where `V` is a scheme, the fibres of `X_V ⟶ V` are
Gorenstein algebraic spaces. -/
@[stacks 0E15]
theorem gorenstein_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyNoetherianFibers f] :
    List.TFAE
      [ Gorenstein f
      , Flat f ∧
          ∃ (V : Over S) (b : ofOver V ⟶ Y),
            (over (@AlgebraicGeometry.Etale)).presheaf b ∧
              Surjective b ∧ residueFibersIsGorenstein (pullbackAlongScheme.snd f b)
      , Flat f ∧
          ∀ (V : Over S) (b : ofOver V ⟶ Y),
            (over (@AlgebraicGeometry.Etale)).presheaf b →
              residueFibersIsGorenstein (pullbackAlongScheme.snd f b) ] :=
  sorry

namespace Gorenstein

/-- A morphism with locally Noetherian fibres is Gorenstein if and only if it is
flat and some surjective étale scheme base change has Gorenstein residue-field
fibres. -/
theorem gorenstein_iff_flat_and_existsSurjectiveEtaleTarget {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyNoetherianFibers f] :
    Gorenstein f ↔ Flat f ∧ existsSurjectiveEtaleTarget f :=
  sorry

/-- A morphism with locally Noetherian fibres is Gorenstein if and only if it is
flat and every étale scheme base change has Gorenstein residue-field fibres. -/
theorem gorenstein_iff_flat_and_forallEtaleTarget {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyNoetherianFibers f] :
    Gorenstein f ↔ Flat f ∧ forallEtaleTarget f :=
  sorry

end Gorenstein

/-- Lemma 76.27.3 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume the fibres of `f` are locally Noetherian.
Given `x` in `|X|` with image `y = Points.map f x` in `|Y|`, `f` is Gorenstein
at `x` if and only if `etaleLocalRingMap f xbar : 𝒪_{Y, ȳ} ⟶ 𝒪_{X, x̄}` is
flat and `etaleLocalRingClosedFiber f xbar` is a Gorenstein local ring, for a
geometric point `xbar` lying over `x`. -/
@[stacks 0E15]
theorem gorensteinAt_iff_etaleLocalRingMap {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyNoetherianFibers f]
    (xbar : GeometricPoint X) (x : Points X) (hx : xbar.liesOver x) :
    gorensteinAt f x ↔
      (etaleLocalRingMap f xbar).Flat ∧
        IsGorensteinLocalRing (etaleLocalRingClosedFiber f xbar) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
