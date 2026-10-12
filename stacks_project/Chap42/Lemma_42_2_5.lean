/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Hom.Multiplicity
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u v

/- Lemma 42.2.5: a morphism of `(2, 1)`-periodic complexes whose source and target
cohomology modules, underlying kernel, and underlying cokernel have finite length preserves
multiplicity. -/
@[stacks 0EA9] #check
  (CategoryTheory.TwoPeriodicEndomorphism.Hom.multiplicity_eq :
    ∀ {R : Type u} [Ring R]
      {K L : CategoryTheory.TwoPeriodicEndomorphism (ModuleCat.{v} R)}
      (f : CategoryTheory.TwoPeriodicEndomorphism.Hom K L)
      (hK₀ : IsFiniteLength R (K.toCochainComplex.homology 0))
      (hK₁ : IsFiniteLength R (K.toCochainComplex.homology 1))
      (hL₀ : IsFiniteLength R (L.toCochainComplex.homology 0))
      (hL₁ : IsFiniteLength R (L.toCochainComplex.homology 1))
      (hker : IsFiniteLength R (kernel f.hom : ModuleCat.{v} R))
      (hcoker : IsFiniteLength R (cokernel f.hom : ModuleCat.{v} R)),
      K.multiplicity hK₀ hK₁ = L.multiplicity hL₀ hL₁)
