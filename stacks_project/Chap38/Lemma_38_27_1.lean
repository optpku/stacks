/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Flattening.FreeAtGenericPoints.Representation
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Flattening

/- Lemma 38.27.1 (1): for every `p : ℕ`, the functor recording rank-`p` freeness at
the generic points of the fibres is represented by a locally closed immersion into `S`. -/
@[stacks 05UC] #check (AlgebraicGeometry.Scheme.Flattening.freeAtGenericPointsFunctor.existsImmersionRepresentation :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [Smooth f] [GeometricallyIrreducible f] (ℱ : X.Modules)
      [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (p : ℕ),
      ∃ Sₚ : Over S,
        Nonempty ((freeAtGenericPointsFunctor f ℱ p).RepresentableBy Sₚ) ∧
          IsImmersion Sₚ.hom)

/- Finite-presentation companion: if `ℱ` is finitely presented, the rank-`p` generic-point
freeness functor has an immersed representing scheme that is finitely presented over `S`. -/
#check (AlgebraicGeometry.Scheme.Flattening.freeAtGenericPointsFunctor.existsImmersionRepresentationOfFinitePresentation :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [Smooth f] [GeometricallyIrreducible f]
      (ℱ : X.Modules) [ℱ.IsFinitePresentation] (p : ℕ),
      ∃ Sₚ : Over S,
        Nonempty ((freeAtGenericPointsFunctor f ℱ p).RepresentableBy Sₚ) ∧
          IsImmersion Sₚ.hom ∧ Scheme.Hom.FinitePresentation Sₚ.hom)

end Flattening
end Scheme
end AlgebraicGeometry
