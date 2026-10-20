/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import ReasLib.RingTheory.Henselian.StrictHenselization
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Topology.NoetherianSpace

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace

universe u v

namespace AlgebraicGeometry.Scheme

/-- For a local ring, connectedness of the punctured spectrum of a strict
henselization implies full faithfulness of finite étale restriction. -/
theorem finiteEtaleBaseChange_fullyFaithful_of_connectedStrictHenselization
    {A : Type u} [CommRing A] [IsLocalRing A] (Ash : Type v)
    [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]
    [ConnectedSpace (PuncturedSpectrum.scheme Ash)] :
    Nonempty
      (finiteEtaleBaseChange (PuncturedSpectrum.puncturedOpen A).ι).FullyFaithful := sorry

/-- A dense quasi-compact open with closed complement points and connected
punctured strict henselizations induces a fully faithful finite étale
restriction functor. -/
theorem finiteEtaleBaseChange_fullyFaithful_of_denseQuasiCompactLocallyConnected
    {X : Scheme.{u}} (U : X.Opens) [QuasiCompact U.ι]
    (h_dense : Dense (U : Set X))
    (h_closed : ∀ x : X, x ∉ U → IsClosed ({x} : Set X))
    (h_conn :
      ∀ (x : X) (hx : x ∉ U) (Ash : Type u) [CommRing Ash]
        [Algebra (X.presheaf.stalk x) Ash]
        [IsStrictHenselizationOf (X.presheaf.stalk x) Ash],
        ConnectedSpace (PuncturedSpectrum.scheme Ash)) :
    Nonempty (finiteEtaleBaseChange U.ι).FullyFaithful := sorry

/-- A dense open in a scheme with finitely many irreducible components on every
quasi-compact open, together with connected punctured strict henselizations on
the complement, induces a fully faithful finite étale restriction functor. -/
theorem finiteEtaleBaseChange_fullyFaithful_of_denseFiniteComponents
    {X : Scheme.{u}} [HasFiniteIrreducibleComponentsOnCompactOpens X] (U : X.Opens)
    (h_dense : Dense (U : Set X))
    (h_conn :
      ∀ (x : X) (hx : x ∉ U) (Ash : Type u) [CommRing Ash]
        [Algebra (X.presheaf.stalk x) Ash]
        [IsStrictHenselizationOf (X.presheaf.stalk x) Ash],
        ConnectedSpace (PuncturedSpectrum.scheme Ash)) :
    Nonempty (finiteEtaleBaseChange U.ι).FullyFaithful := sorry

/-- For a Noetherian scheme, a dense open with connected punctured strict
henselizations on its complement induces a fully faithful finite étale
restriction functor when the underlying topological space is Noetherian. -/
theorem finiteEtaleBaseChange_fullyFaithful_of_noetherianDensePuncturedConnected
    {X : Scheme.{u}} [NoetherianSpace X] (U : X.Opens)
    (h_dense : Dense (U : Set X))
    (h_conn :
      ∀ (x : X) (hx : x ∉ U) (Ash : Type u) [CommRing Ash]
        [Algebra (X.presheaf.stalk x) Ash]
        [IsStrictHenselizationOf (X.presheaf.stalk x) Ash],
        ConnectedSpace (PuncturedSpectrum.scheme Ash)) :
    Nonempty (finiteEtaleBaseChange U.ι).FullyFaithful := sorry

end AlgebraicGeometry.Scheme
