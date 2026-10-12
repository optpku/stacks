/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard

/-!
# Picard groups of UFD schemes

This file owns triviality results for Picard groups of spectra of unique factorization domains,
their open subschemes, and affine spaces over them.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry SpecOfNotation

universe u

namespace AlgebraicGeometry.Scheme

/-- The Picard group of the spectrum of a unique factorization domain is trivial. -/
@[stacks 0BDA]
instance subsingleton_picardGroup_Spec_of_uniqueFactorizationMonoid
    (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] :
    Subsingleton (PicardGroup (Spec(R))) := sorry

/-- The Picard group of every open subscheme of the spectrum of a unique factorization domain
is trivial. -/
@[stacks 0BDA]
instance subsingleton_picardGroup_openSubscheme_Spec_of_uniqueFactorizationMonoid
    (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (U : (Spec(R)).Opens) :
    Subsingleton (PicardGroup U.toScheme) := sorry

/-- The Picard group of affine `n`-space over a unique factorization domain is trivial. -/
@[stacks 0BDA]
instance subsingleton_picardGroup_affineSpace_of_uniqueFactorizationMonoid
    (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] (n : ℕ) :
    Subsingleton (PicardGroup (𝔸(ULift.{u} (Fin n); Spec(R)))) := sorry

namespace PicardGroup

/-- The Picard group of every open subscheme of affine `n`-space over a unique factorization
domain is trivial. -/
@[stacks 0BDA]
instance instSubsingletonOpenAffineSpace
    (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] (n : ℕ)
    (U : (𝔸(ULift.{u} (Fin n); Spec(R))).Opens) :
    Subsingleton (PicardGroup U.toScheme) := sorry

end PicardGroup

/-- The Picard group of every open subscheme of affine `n`-space over a field is trivial. -/
@[stacks 0BDA]
theorem subsingleton_picardGroup_openSubscheme_affineSpace_of_field
    (k : Type u) [Field k] (n : ℕ)
    (U : (𝔸(ULift.{u} (Fin n); Spec(k))).Opens) :
    Subsingleton (PicardGroup U.toScheme) := sorry

end AlgebraicGeometry.Scheme
