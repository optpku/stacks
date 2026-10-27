/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Gorenstein.Global
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Gorenstein.Fiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Fiber

/-!
# Fibrewise characterizations of Gorenstein morphisms

Flatness and Gorenstein fibres characterize Gorenstein morphisms with locally
Noetherian fibres, both globally and on étale local rings.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- For a morphism with locally Noetherian fibres, Gorensteinness is equivalent
to flatness and Gorenstein residue-field fibres after some surjective étale
scheme chart, equivalently after every étale scheme chart. -/
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

/-- At a point of a morphism with locally Noetherian fibres, Gorensteinness
is equivalent to flatness of the canonical étale local-ring map and
Gorensteinness of its closed fibre. -/
theorem gorensteinAt_iff_etaleLocalRingMap {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyNoetherianFibers f]
    (xbar : GeometricPoint X) (x : Points X) (hx : xbar.liesOver x) :
    GorensteinAt f x ↔
      (etaleLocalRingMap f xbar).Flat ∧
        IsGorensteinLocalRing (fiberEtaleLocalRing f xbar) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
