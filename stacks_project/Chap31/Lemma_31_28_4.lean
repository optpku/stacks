/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.UniqueFactorization
import StacksCheckRecall

/-!
# Lemma 31.28.4

Triviality of Picard groups of UFD spectra and their open subschemes.

@stack 0BDA
-/

@[expose] public section

universe u

/- Lemma 31.28.4 (1): the Picard group of the spectrum of a unique factorization domain is
trivial. -/
@[stacks 0BDA] #check
  (AlgebraicGeometry.Scheme.subsingleton_picardGroup_Spec_of_uniqueFactorizationMonoid :
    ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R],
      Subsingleton
        (AlgebraicGeometry.Scheme.PicardGroup
          (AlgebraicGeometry.Spec (CommRingCat.of R))))

/- Lemma 31.28.4 (2): the Picard group of every open subscheme of the spectrum of a unique
factorization domain is trivial. -/
@[stacks 0BDA] #check
  (AlgebraicGeometry.Scheme.subsingleton_picardGroup_openSubscheme_Spec_of_uniqueFactorizationMonoid :
    ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
      (U : (AlgebraicGeometry.Spec (CommRingCat.of R)).Opens),
      Subsingleton (AlgebraicGeometry.Scheme.PicardGroup U.toScheme))

/- Lemma 31.28.4 (3): the Picard group of affine `n`-space over a unique factorization domain
is trivial. -/
@[stacks 0BDA] #check
  (AlgebraicGeometry.Scheme.subsingleton_picardGroup_affineSpace_of_uniqueFactorizationMonoid :
    ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] (n : ℕ),
      Subsingleton (AlgebraicGeometry.Scheme.PicardGroup
        (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin n))
          (AlgebraicGeometry.Spec (CommRingCat.of R)))))

/- Lemma 31.28.4 (4): the Picard group of every open subscheme of affine `n`-space over a unique
factorization domain is trivial. -/
@[stacks 0BDA] #check
  (AlgebraicGeometry.Scheme.PicardGroup.instSubsingletonOpenAffineSpace :
    ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] (n : ℕ)
      (U : (AlgebraicGeometry.AffineSpace
        (ULift.{u} (Fin n)) (AlgebraicGeometry.Spec (CommRingCat.of R))).Opens),
      Subsingleton (AlgebraicGeometry.Scheme.PicardGroup U.toScheme))

/- Lemma 31.28.4 (5): the Picard group of every open subscheme of affine `n`-space over a field
is trivial. -/
@[stacks 0BDA] #check
  (AlgebraicGeometry.Scheme.subsingleton_picardGroup_openSubscheme_affineSpace_of_field :
    ∀ (k : Type u) [Field k] (n : ℕ)
      (U : (AlgebraicGeometry.AffineSpace
        (ULift.{u} (Fin n)) (AlgebraicGeometry.Spec (CommRingCat.of k))).Opens),
      Subsingleton (AlgebraicGeometry.Scheme.PicardGroup U.toScheme))
