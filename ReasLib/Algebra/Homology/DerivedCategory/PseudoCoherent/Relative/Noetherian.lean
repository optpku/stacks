module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Derived

/-!
# Relative pseudo-coherence over a Noetherian base

@stack 067F

Over a Noetherian base, relative pseudo-coherence has the expected
bounded-above finite-cohomology and finite-module characterizations.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open DerivedCategory.TStructure

universe u v

namespace CategoryTheory.DerivedCategory

/-- Lemma 15.82.17 (1) (067F): over a Noetherian base, a derived `A`-complex is
`m`-pseudo-coherent relative to `R` exactly
when it is bounded above and its cohomology is finite in degrees at least `m`. -/
@[stacks 067F "(1), Noetherian relative m-pseudo-coherence"]
theorem isMPseudoCoherentRelativeTo_iff_boundedAbove_and_homology_finite_ge
    {R : Type u} {A : Type v} [CommRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (K : DerivedCategory (ModuleCat A)) (m : ℤ) :
    K.IsMPseudoCoherentRelativeTo R m ↔
      (t.minus : ObjectProperty (DerivedCategory (ModuleCat A))) K ∧
        ∀ i : ℤ, m ≤ i →
          Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj K) := sorry

/-- Lemma 15.82.17 (2) (067F): over a Noetherian base, a derived `A`-complex is pseudo-coherent relative to `R` exactly
when it is bounded above and all of its cohomology modules are finite. -/
@[stacks 067F "(2), Noetherian relative pseudo-coherence"]
theorem isPseudoCoherentRelativeTo_iff_boundedAbove_and_homology_finite
    {R : Type u} {A : Type v} [CommRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (K : DerivedCategory (ModuleCat A)) :
    K.IsPseudoCoherentRelativeTo R ↔
      (t.minus : ObjectProperty (DerivedCategory (ModuleCat A))) K ∧
        ∀ i : ℤ, Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj K) := sorry

end CategoryTheory.DerivedCategory

namespace Module

/-- Lemma 15.82.17 (3) (067F): over a Noetherian base, an `A`-module is pseudo-coherent relative to `R` exactly when it is a
finite `A`-module. -/
@[stacks 067F "(3), Noetherian relative pseudo-coherent module"]
theorem isPseudoCoherentRelativeTo_iff_finite
    {R : Type u} {A : Type v} [CommRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] {M : Type v} [AddCommGroup M] [Module A M] :
    Module.IsPseudoCoherentRelativeTo R A M ↔ Module.Finite A M := sorry

end Module
