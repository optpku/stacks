/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Example_90_11_14_TangentSpaceMap

/-!
# Tangent-space map of a prorepresentable functor

A morphism `f : R ⟶ S` in `Ĉ_Λ` induces a transformation of restricted coyoneda
functors, hence a `k`-linear map of tangent spaces identified with restriction of
`Λ`-derivations into `k`.
-/

@[expose] public section

open CategoryTheory
open CompleteLocalAlgCat
open Functor.IsPredeformationFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor.IsPredeformationFunctor

/-- Example 90.11.14: a morphism `f : R ⟶ S` in `Ĉ_Λ` induces `G ⟶ F` for
`F = restrictedCoyoneda R` and `G = restrictedCoyoneda S`, hence a `k`-linear map
`TG → TF`. Under the identifications `TF ≃ Derivation Λ R.carrier k` and
`TG ≃ Derivation Λ S.carrier k` of Example 90.11.11, this is the restriction
`Hom.mapDerivation f`. -/
@[stacks 06ST]
theorem tangentSpaceEquivDerivation_map {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S)
    (x : tangentSpace (restrictedCoyoneda S)) :
    tangentSpaceEquivDerivation R (tangentSpaceMap f x) =
      Hom.mapDerivation f (tangentSpaceEquivDerivation S x) :=
  sorry

end CategoryTheory.Functor.IsPredeformationFunctor
