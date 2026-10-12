/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.ProjectiveSpace.Picard
import StacksCheckRecall

noncomputable section

universe u

/- Lemma 31.28.5 (1): over a unique factorization domain, the Picard group of positive-dimensional
standard projective space is `ℤ`, with `m` corresponding to `𝒪(m)`. -/
@[stacks 0BXJ] #check
  (AlgebraicGeometry.ProjectiveSpace.existsIntAddEquivPicardGroupOfUniqueFactorizationMonoid :
    ∀ (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
      (n : ℕ), 0 < n →
      ∃ e : ℤ ≃+ (AlgebraicGeometry.ProjectiveSpace.scheme R n).PicardGroup,
        ∀ m : ℤ, e m =
          AlgebraicGeometry.Scheme.Modules.picardClass
            (AlgebraicGeometry.ProjectiveSpace.twistingSheaf R n m))

/- Lemma 31.28.5 (2): over a field, the Picard group of positive-dimensional standard projective
space is `ℤ`, with `m` corresponding to `𝒪(m)`. -/
@[stacks 0BXJ] #check
  (AlgebraicGeometry.ProjectiveSpace.existsIntAddEquivPicardGroupOfField :
    ∀ (k : Type u) [Field k] (n : ℕ), 0 < n →
      ∃ e : ℤ ≃+ (AlgebraicGeometry.ProjectiveSpace.scheme k n).PicardGroup,
        ∀ m : ℤ, e m =
          AlgebraicGeometry.Scheme.Modules.picardClass
            (AlgebraicGeometry.ProjectiveSpace.twistingSheaf k n m))
