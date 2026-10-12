/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Perfect.ResidueField
import StacksCheckRecall

/-!
# Lemma 15.84.10

@stack 0GHJ
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

/- Lemma 15.84.10 (0GHJ): relative perfectness over a flat finitely presented base is detected
by boundedness below of the object and of every derived residue-field fiber. -/
@[stacks 0GHJ "relative perfectness detected by bounded residue-field fibers"]
#check fun {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (K : DerivedCategory (ModuleCat A)) (hK : K.IsPseudoCoherent) =>
  (DerivedCategory.isPerfectOver_iff_boundedBelow_and_primeResidueFields_boundedBelow K hK :
    K.IsPerfectOver R ↔
      (∃ n : ℤ, K.IsGE n) ∧
        ∀ p : PrimeSpectrum R, ∃ n : ℤ,
          ((ModuleCat.derivedExtensionOfScalars
            (algebraMap R p.asIdeal.ResidueField)).obj
            ((ModuleCat.derivedRestrictionOfScalars (algebraMap R A)).obj K)).IsGE n)

/- The intrinsic predicate combines pseudo-coherence over the algebra with finite Tor dimension
after derived restriction to the base. -/
#check @DerivedCategory.IsPerfectOver
#check @DerivedCategory.IsPerfectOver.isPseudoCoherent
#check @DerivedCategory.IsPerfectOver.hasFiniteTorDimensionOver

/- Residue-field fibers are formed by the canonical derived extension functor. -/
#check @ModuleCat.derivedExtensionOfScalars

end
