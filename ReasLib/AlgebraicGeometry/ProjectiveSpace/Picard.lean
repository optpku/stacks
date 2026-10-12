/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.ZMod.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist.Invertible
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.OpenComplement
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.UniqueFactorization

/-!
# Picard groups of standard projective spaces

This module describes Picard groups of standard projective spaces and of projective lines
punctured at closed points.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveSpace

/-- Over a unique factorization domain, the Picard group of positive-dimensional standard
projective space is additively equivalent to `ℤ`, with `m` corresponding to `𝒪(m)`. -/
theorem existsIntAddEquivPicardGroupOfUniqueFactorizationMonoid
    (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (n : ℕ) (hn : 0 < n) :
    ∃ e : ℤ ≃+ (scheme R n).PicardGroup,
      ∀ m : ℤ, e m = Scheme.Modules.picardClass (twistingSheaf R n m) := sorry

/-- Over a field, the Picard group of positive-dimensional standard projective space is
additively equivalent to `ℤ`, with `m` corresponding to `𝒪(m)`. -/
theorem existsIntAddEquivPicardGroupOfField
    (k : Type u) [Field k] (n : ℕ) (hn : 0 < n) :
    ∃ e : ℤ ≃+ (scheme k n).PicardGroup,
      ∀ m : ℤ, e m = Scheme.Modules.picardClass (twistingSheaf k n m) := sorry

/-- Every invertible module on positive-dimensional standard projective space is isomorphic to
some canonical twisting sheaf. -/
theorem existsIsoTwistingSheaf
    (k : Type u) [Field k] (n : ℕ) (hn : 0 < n)
    (L : (scheme k n).Modules) [Scheme.Modules.Invertible L] :
    ∃ d : ℤ, CategoryTheory.IsIsomorphic L (twistingSheaf k n d) := sorry

/-- Restriction from a projective line to the complement of a closed point is surjective on
Picard groups. -/
theorem picardPullback_surjective_puncturedLine
    (k : Type u) [Field k]
    (t : scheme k 1) (ht : t ∈ closedPoints (scheme k 1))
    (U : (scheme k 1).Opens)
    (hU : (U : Set (scheme k 1)) = ({t} : Set (scheme k 1))ᶜ) :
    Function.Surjective (Scheme.Hom.picardPullback U.ι) := sorry

/-- The Picard group of a projective line punctured at a closed point is cyclic, with modulus
the residue degree of that point over the base field. -/
theorem nonempty_picardGroup_puncturedLine_equiv_zmod_residueDegree
    (k : Type u) [Field k]
    (t : scheme k 1) (ht : t ∈ closedPoints (scheme k 1))
    (U : (scheme k 1).Opens)
    (hU : (U : Set (scheme k 1)) = ({t} : Set (scheme k 1))ᶜ) :
    Nonempty
      (U.toScheme.PicardGroup ≃+
        ZMod ((toSpec k 1).residueDegree t)) := sorry

/-- Removing a non-rational closed point from a projective line gives a nontrivial Picard
group. -/
theorem nontrivial_picardGroup_puncturedLine_of_not_rational
    (k : Type u) [Field k]
    (t : scheme k 1) (ht : t ∈ closedPoints (scheme k 1))
    (U : (scheme k 1).Opens)
    (hU : (U : Set (scheme k 1)) = ({t} : Set (scheme k 1))ᶜ)
    (ht_not_rational : ¬ CategoryTheory.IsIso ((toSpec k 1).residueFieldMap t)) :
    Nontrivial U.toScheme.PicardGroup := sorry

/-- After a field extension receiving the residue field of the removed point compatibly with
the base field, the Picard group of the base-changed punctured projective line is trivial. -/
theorem subsingleton_picardGroup_puncturedLine_baseChange
    (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    (t : scheme k 1) (ht : t ∈ closedPoints (scheme k 1))
    (U : (scheme k 1).Opens)
    (hU : (U : Set (scheme k 1)) = ({t} : Set (scheme k 1))ᶜ)
    (ι : (scheme k 1).residueField t →+* k')
    (hι : ι.comp (Scheme.Hom.ResidueField.mapOfSpec (toSpec k 1) t) =
      algebraMap k k') :
    Subsingleton
      (FieldExtension.baseChange k k' (U.ι ≫ toSpec k 1)).PicardGroup := sorry

end AlgebraicGeometry.ProjectiveSpace
