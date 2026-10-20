module

public import Mathlib.RingTheory.FiniteStability
public import ReasLib.Algebra.Category.ModuleCat.Tor.Independence
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.ChangeOfRings
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Derived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tor-independent base change for relative pseudo-coherence

The source-facing base-change object is written using the explicit derived extension functor.
The Tor-independence input is the bundled `ModuleCat.Tor.IsIndependent` predicate, so this leaf
does not depend on a chapter-local algebra abbreviation.

@stack 067A
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace CategoryTheory.DerivedCategory

-- Local instance justification (instance diamond): use the right tensor-factor algebra only for
-- this Tor-independent base-change comparison.
attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']

local notation "Aprime" => A ⊗[R] R'

/-- Lemma 15.82.12 (067A): the explicit derived base-change object. -/
@[stacks 067A "derived tensor base-change object"]
noncomputable abbrev torIndependentBaseChange (K : DerivedCategory (ModuleCat A)) :
    DerivedCategory (ModuleCat Aprime) :=
  (ModuleCat.derivedExtensionOfScalars (algebraMap A Aprime)).obj K

/-- Lemma 15.82.12 (067A), bounded clause: Tor-independent base change preserves relative
`m`-pseudo-coherence. -/
@[stacks 067A "Tor-independent base change of relative m-pseudo-coherence"]
theorem isMPseudoCoherentRelativeTo_torIndependentBaseChange
    [Algebra.FiniteType R A]
    (K : DerivedCategory (ModuleCat A)) (m : ℤ)
    (hTor : ModuleCat.Tor.IsIndependent (ModuleCat.of R A) (ModuleCat.of R R'))
    (hK : K.IsMPseudoCoherentRelativeTo R m) :
    letI : Algebra.FiniteType R' Aprime :=
      Algebra.FiniteType.equiv (Algebra.FiniteType.baseChange R')
        (Algebra.TensorProduct.commRight R R' A)
    (torIndependentBaseChange (R := R) (A := A) (R' := R') K).IsMPseudoCoherentRelativeTo R' m := sorry

/-- Lemma 15.82.12 (067A), unbounded clause: Tor-independent base change preserves relative
pseudo-coherence. -/
@[stacks 067A "Tor-independent base change of relative pseudo-coherence"]
theorem isPseudoCoherentRelativeTo_torIndependentBaseChange
    [Algebra.FiniteType R A]
    (K : DerivedCategory (ModuleCat A))
    (hTor : ModuleCat.Tor.IsIndependent (ModuleCat.of R A) (ModuleCat.of R R'))
    (hK : K.IsPseudoCoherentRelativeTo R) :
    letI : Algebra.FiniteType R' Aprime :=
      Algebra.FiniteType.equiv (Algebra.FiniteType.baseChange R')
        (Algebra.TensorProduct.commRight R R' A)
    (torIndependentBaseChange (R := R) (A := A) (R' := R') K).IsPseudoCoherentRelativeTo R' := sorry

end CategoryTheory.DerivedCategory

end
