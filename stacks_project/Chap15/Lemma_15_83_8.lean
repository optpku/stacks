/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Surjective
import StacksCheckRecall

/-!
# Lemma 15.83.8 (0E1T)

@stack 0E1T
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

/- The surjective restriction bridge used in both clauses of Lemma 15.83.8. -/
#check @CategoryTheory.DerivedCategory.isMPseudoCoherentRelativeTo_iff_restrictScalars_of_surjective
#check @CategoryTheory.DerivedCategory.isPseudoCoherentRelativeTo_iff_restrictScalars_of_surjective

/- Lemma 15.83.8 (1): the five absolute, relative, and restricted forms of pseudo-coherence are
equivalent. -/
@[stacks 0E1T "(1), pseudo-coherence across a surjective change of rings"]
#check fun {R B A : Type u} [CommRing R] [CommRing B] [CommRing A]
    [Algebra R B] [Algebra B A] [Algebra R A] [IsScalarTower R B A]
    [Module.Flat R B] [Algebra.FinitePresentation R B]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (K : DerivedCategory (ModuleCat A)) (hφ : Function.Surjective (algebraMap B A)) =>
  (CategoryTheory.DerivedCategory.pseudoCoherent_tfae_of_surjective_of_flat_finitePresentation
    K hφ : List.TFAE [
      K.IsPseudoCoherent,
      K.IsPseudoCoherentRelativeTo R,
      K.IsPseudoCoherentRelativeTo A,
      ((ModuleCat.derivedRestrictionOfScalars (algebraMap B A)).obj K).IsPseudoCoherent,
      ((ModuleCat.derivedRestrictionOfScalars
        (algebraMap B A)).obj K).IsPseudoCoherentRelativeTo R
    ])

/- Lemma 15.83.8 (2): the analogous five forms of `m`-pseudo-coherence are equivalent. -/
@[stacks 0E1T "(2), m-pseudo-coherence across a surjective change of rings"]
#check fun {R B A : Type u} [CommRing R] [CommRing B] [CommRing A]
    [Algebra R B] [Algebra B A] [Algebra R A] [IsScalarTower R B A]
    [Module.Flat R B] [Algebra.FinitePresentation R B]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (K : DerivedCategory (ModuleCat A)) (m : ℤ)
    (hφ : Function.Surjective (algebraMap B A)) =>
  (CategoryTheory.DerivedCategory.mPseudoCoherent_tfae_of_surjective_of_flat_finitePresentation
    K m hφ : List.TFAE [
      K.IsMPseudoCoherent m,
      K.IsMPseudoCoherentRelativeTo R m,
      K.IsMPseudoCoherentRelativeTo A m,
      ((ModuleCat.derivedRestrictionOfScalars (algebraMap B A)).obj K).IsMPseudoCoherent m,
      ((ModuleCat.derivedRestrictionOfScalars
        (algebraMap B A)).obj K).IsMPseudoCoherentRelativeTo R m
    ])
