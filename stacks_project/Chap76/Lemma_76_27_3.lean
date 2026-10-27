/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Gorenstein.Locality

/-!
# Characterizations of Gorenstein morphisms of algebraic spaces

Both global Gorensteinness and Gorensteinness at a point are characterized by
flatness and Gorenstein fibres when the fibres are locally Noetherian.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.27.3 (1): Global Gorensteinness is equivalent to flatness and
Gorenstein fibres after some, equivalently every, étale scheme chart. -/
@[stacks 0E15] #check (AlgebraicGeometry.AlgebraicSpace.gorenstein_tfae :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyNoetherianFibers f],
    List.TFAE
      [ Gorenstein f
      , Flat f ∧
          ∃ (V : Over S) (b : ofOver V ⟶ Y),
            (over (@AlgebraicGeometry.Etale)).presheaf b ∧
              Surjective b ∧ residueFibersIsGorenstein (pullbackAlongScheme.snd f b)
      , Flat f ∧
          ∀ (V : Over S) (b : ofOver V ⟶ Y),
            (over (@AlgebraicGeometry.Etale)).presheaf b →
              residueFibersIsGorenstein (pullbackAlongScheme.snd f b) ])

#check (AlgebraicGeometry.AlgebraicSpace.Gorenstein.gorenstein_iff_flat_and_existsSurjectiveEtaleTarget :
  ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyNoetherianFibers f],
    Gorenstein f ↔ Flat f ∧ Gorenstein.existsSurjectiveEtaleTarget f)

#check (AlgebraicGeometry.AlgebraicSpace.Gorenstein.gorenstein_iff_flat_and_forallEtaleTarget :
  ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyNoetherianFibers f],
    Gorenstein f ↔ Flat f ∧ Gorenstein.forallEtaleTarget f)

/- Lemma 76.27.3 (2): Gorensteinness at a point is equivalent to flatness of
the canonical étale local-ring map and Gorensteinness of its closed fibre. -/
@[stacks 0E15] #check (AlgebraicGeometry.AlgebraicSpace.gorensteinAt_iff_etaleLocalRingMap :
  ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyNoetherianFibers f]
    (xbar : GeometricPoint X) (x : Points X) (hx : xbar.liesOver x),
    GorensteinAt f x ↔
      (etaleLocalRingMap f xbar).Flat ∧
        IsGorensteinLocalRing (fiberEtaleLocalRing f xbar))

end AlgebraicGeometry.AlgebraicSpace
