/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Flattening.InDimensions
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity
public import ReasLib.AlgebraicGeometry.Scheme.Module.CompleteDevissageOver
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.LocalGeneration
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

/-!
# Representability of the flat-in-dimensions functor

This module records local and global representability results for the flat-in-dimensions functor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Flattening.flatInDimensionsFunctor

/-- If a finitely presented module admits a complete dévissage over `s` and is flat in
dimensions at least `d + 1`, then near `s` its degree-`d` flattening functor is represented by
a finitely presented monomorphism. -/
theorem existsMonomorphismRepresentationNear {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.FinitePresentation f] (ℱ : X.Modules) [ℱ.IsFinitePresentation]
    (s : S) (d : ℕ) (h_devissage : Nonempty (Modules.CompleteDevissageOver f ℱ s))
    (h_flat : Modules.flatOverInDimensionsGE ℱ f (d + 1)) :
    ∃ U : S.Opens, s ∈ U ∧
      ∃ Z : Over U.toScheme,
        Nonempty
          ((flatInDimensionsFunctor (pullback.snd f U.ι)
            (Modules.baseChangeModule f U.ι ℱ) d).RepresentableBy Z) ∧
          Mono Z.hom ∧ Scheme.Hom.FinitePresentation Z.hom := sorry

/-- For a finitely presented morphism and a finitely presented module pure relative to the base,
the degree-`n` flat-in-dimensions functor is represented by a finitely presented monomorphism. -/
theorem existsMonomorphismRepresentation {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.FinitePresentation f] (ℱ : X.Modules) [ℱ.IsFinitePresentation]
    (n : ℕ) (h_pure : ℱ.IsPureOver f) :
    ∃ Z : Over S,
      Nonempty ((flatInDimensionsFunctor f ℱ n).RepresentableBy Z) ∧
        Mono Z.hom ∧ Scheme.Hom.FinitePresentation Z.hom := sorry

end AlgebraicGeometry.Scheme.Flattening.flatInDimensionsFunctor
