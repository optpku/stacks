module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.RelativeCotangent

/-!
# Tangent space of a classical or separable prorepresentable functor

For `F = restrictedCoyoneda S`, Example 90.11.11 identifies
`tangentSpace F` with `Derivation Λ S.carrier k`. In the classical case, and
more generally when `k / residueImage Λ k` is separable, this pairs
bijectively with the linear dual of `relativeCotangentSpace S`. The formula
`TF = T_{S/Λ}` denotes this dual pairing `tangentSpaceToRelativeCotangentDual`.
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

/- Example 90.11.12 (1): in the classical case, the tangent space of
`F = restrictedCoyoneda S` identifies with the linear dual of the relative
cotangent quotient of `S` over `Λ` through the canonical pairing. -/
@[stacks 06SS]
#check (CategoryTheory.Functor.IsPredeformationFunctor.bijective_tangentSpaceToRelativeCotangentDual_isClassical :
  ∀ (S : CompleteLocalAlgCat Λ k) [ArtinianLocalAlgCat.IsClassical Λ k],
    Function.Bijective
      (CategoryTheory.Functor.IsPredeformationFunctor.tangentSpaceToRelativeCotangentDual S))

/- Example 90.11.12 (2): more generally, when `k / residueImage Λ k` is
separable, `tangentSpaceToRelativeCotangentDual S` is bijective. See
Exercise 111.35.2. -/
@[stacks 06SS]
#check (CategoryTheory.Functor.IsPredeformationFunctor.bijective_tangentSpaceToRelativeCotangentDual :
  ∀ (S : CompleteLocalAlgCat Λ k) [Algebra.IsSeparable (Algebra.residueImage Λ k) k],
    Function.Bijective
      (CategoryTheory.Functor.IsPredeformationFunctor.tangentSpaceToRelativeCotangentDual S))

end CategoryTheory.Functor.IsPredeformationFunctor
