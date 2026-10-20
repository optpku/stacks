/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints.Relative

/-!
# Lemma 71.4.4

Weak association on fibres is independent of étale charts and field-valued
representatives. On locally Noetherian fibres the chart and monomorphic
conditions can be expressed using associated points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules.RelativeWeakAss

universe u

/- Lemma 71.4.4 (1).
The five equivalent weak-association conditions. -/
@[stacks 0CUZ] #check (AlgebraicGeometry.AlgebraicSpace.Modules.RelativeWeakAss.relativeWeakAss_tfae :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (F : X.Modules) [F.IsQuasicoherent] (x : Points X),
    List.TFAE [existsEtale f F x, forallEtale f F x, existsOverPullback f F x,
      forallOverPullback f F x, existsField f F x])

/- Lemma 71.4.4 (2).
The equivalence for a monomorphic field-valued representative. -/
@[stacks 0CUZ] #check (AlgebraicGeometry.AlgebraicSpace.Modules.RelativeWeakAss.relativeWeakAss_iff_of_mono :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (F : X.Modules) [F.IsQuasicoherent] (x : Points X)
    (p₀ : FieldValuedPoint Y) [Mono p₀.hom]
    (hp₀ : Points.mk p₀ = Points.map f x),
    ofMono f F x p₀ ↔ existsField f F x)

/- Lemma 71.4.4 (3).
Associated-point replacement on locally Noetherian fibres. -/
@[stacks 0CUZ] #check (AlgebraicGeometry.AlgebraicSpace.Modules.RelativeWeakAss.associatedPoints_fiber_tfae :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (F : X.Modules) [F.IsQuasicoherent] (x : Points X)
    [IsLocallyNoetherianFiber f (Points.map f x)],
    List.TFAE [existsEtale f F x, forallEtale f F x, existsOverPullback f F x,
      forallOverPullback f F x, existsField f F x, existsEtaleAss f F x,
      forallEtaleAss f F x, existsOverPullbackAss f F x, forallOverPullbackAss f F x])

#check (AlgebraicGeometry.AlgebraicSpace.Modules.RelativeWeakAss.ofMonoAss_iff_ofMono :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (F : X.Modules)
    [F.IsQuasicoherent] (x : Points X) (p₀ : FieldValuedPoint Y) [Mono p₀.hom]
    (hp₀ : Points.mk p₀ = Points.map f x)
    [IsLocallyNoetherianFiber f (Points.map f x)],
    ofMonoAss f F x p₀ ↔ ofMono f F x p₀)

#check (AlgebraicGeometry.AlgebraicSpace.existsUnique_fieldFiber_point_of_mono :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X)
    (p₀ : FieldValuedPoint Y) [Mono p₀.hom]
    (hp₀ : Points.mk p₀ = Points.map f x),
    ∃! t : Points (fieldFiber f p₀), Points.map (fieldFiberι f p₀) t = x)
