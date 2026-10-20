/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Flattening.Representability
public import ReasLib.RingTheory.Ideal.FlatQuotient

/-!
# Flattening over an Artinian spectrum

This module gives the closed-immersion representation of the flattening functor over the
spectrum of an Artinian ring.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules.Flattening

/-- Over the spectrum of an Artinian ring, the flattening functor of a quasicoherent module
has a representing scheme whose structure morphism is a closed immersion. -/
theorem exists_closedImmersion_representation {R : Type u} [CommRing R] [IsArtinianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    ∃ S' : Over (Spec (CommRingCat.of R)),
      Nonempty ((functor f ℱ).RepresentableBy S') ∧ IsClosedImmersion S'.hom := sorry

/-- The flattening functor of a quasicoherent module over an Artinian spectrum is
representable. -/
instance functor.instIsRepresentableOfIsArtinian {R : Type u} [CommRing R]
    [IsArtinianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    (functor f ℱ).IsRepresentable := sorry

/-- The chosen representing scheme for a flattening functor over an Artinian spectrum is a
closed subscheme of that spectrum. -/
instance instIsClosedImmersionReprX {R : Type u} [CommRing R] [IsArtinianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsClosedImmersion (Functor.reprX (functor f ℱ)).hom := sorry

end AlgebraicGeometry.Scheme.Modules.Flattening
