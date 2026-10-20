/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.RelativeCotangent
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.ProrepresentableTangent

/-!
# Relative cotangent duals of prorepresentable tangent spaces

The tangent space of restricted coyoneda pairs canonically with the relative
cotangent quotient of the representing complete local algebra. The pairing is
bijective for a separable residue extension, in particular in the classical case.
-/

@[expose] public section

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

noncomputable section

namespace CategoryTheory.Functor.IsPredeformationFunctor

open CompleteLocalAlgCat

/-- The canonical linear pairing of a prorepresentable tangent space with the
relative cotangent quotient of its representing complete local algebra. -/
def tangentSpaceToRelativeCotangentDual (S : CompleteLocalAlgCat Λ k) :
    tangentSpace (restrictedCoyoneda S) →ₗ[k] (relativeCotangentSpace S →ₗ[k] k) :=
  (derivationToRelativeCotangentDual S).comp (tangentSpaceLinearEquivDerivation S).toLinearMap

/-- The tangent pairing evaluates as its associated derivation on maximal-ideal representatives. -/
theorem tangentSpaceToRelativeCotangentDual_apply (S : CompleteLocalAlgCat Λ k)
    (x : tangentSpace (restrictedCoyoneda S)) (y : S.maximalIdeal) :
    tangentSpaceToRelativeCotangentDual S x (RelativeCotangentSpace.mk S y) =
      tangentSpaceEquivDerivation S x (y : S.carrier) := sorry

/-- For a separable residue extension, the canonical tangent pairing identifies
a prorepresentable tangent space with the linear dual of the relative cotangent quotient. -/
theorem bijective_tangentSpaceToRelativeCotangentDual (S : CompleteLocalAlgCat Λ k)
    [Algebra.IsSeparable (Algebra.residueImage Λ k) k] :
    Function.Bijective (tangentSpaceToRelativeCotangentDual S) := sorry

/-- In the classical case, the canonical tangent pairing identifies a prorepresentable
tangent space with the linear dual of the relative cotangent quotient. -/
theorem bijective_tangentSpaceToRelativeCotangentDual_isClassical (S : CompleteLocalAlgCat Λ k)
    [ArtinianLocalAlgCat.IsClassical Λ k] :
    Function.Bijective (tangentSpaceToRelativeCotangentDual S) := sorry

end CategoryTheory.Functor.IsPredeformationFunctor

end
