/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Example_90_11_12_RelativeCotangent

/-!
# Tangent space of a classical or separable prorepresentable functor

For `F = restrictedCoyoneda S`, Example 90.11.11 identifies
`tangentSpace F` with `Derivation Λ S.carrier k`. In the classical case, and
more generally when `k / residueImage Λ k` is separable, this pairs
bijectively with `relativeCotangentSpace S`, so `TF = T_{S/Λ}` as the dual
pairing `tangentSpaceToRelativeCotangentDual`.
-/

@[expose] public section

open CategoryTheory
open CompleteLocalAlgCat
open Functor.IsPredeformationFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

variable (S : CompleteLocalAlgCat Λ k)

namespace CategoryTheory.Functor.IsPredeformationFunctor

/-- Example 90.11.12 (1): in the classical case, the tangent space of
`F = restrictedCoyoneda S` is identified with the relative cotangent space of
`S` over `Λ` by bijectivity of `tangentSpaceToRelativeCotangentDual S`. The
formula `TF = T_{S/Λ}` is this dual pairing. -/
@[stacks 06SS]
theorem bijective_tangentSpaceToRelativeCotangentDual_isClassical
    [ArtinianLocalAlgCat.IsClassical Λ k] :
    Function.Bijective (tangentSpaceToRelativeCotangentDual S) := sorry

/-- Example 90.11.12 (2): more generally, when `k / residueImage Λ k` is
separable, `tangentSpaceToRelativeCotangentDual S` is bijective. See
Exercise 111.35.2. -/
@[stacks 06SS]
theorem bijective_tangentSpaceToRelativeCotangentDual
    [Algebra.IsSeparable (Algebra.residueImage Λ k) k] :
    Function.Bijective (tangentSpaceToRelativeCotangentDual S) := sorry

end CategoryTheory.Functor.IsPredeformationFunctor
