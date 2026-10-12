/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Example_90_11_11_Derivation
public import stacks_project.Chap90.Lemma_90_4_6_Derivation
public import stacks_project.Chap90.Lemma_90_8_6_Coyoneda

/-!
# Tangent-space maps of restricted coyoneda functors

A morphism `f : R ⟶ S` in `CompleteLocalAlgCat Λ k` induces a `k`-linear map
on the tangent spaces of the restricted coyoneda functors
`restrictedCoyoneda S` and `restrictedCoyoneda R`.
-/

@[expose] public section

open CategoryTheory
open CompleteLocalAlgCat

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

noncomputable section

namespace CategoryTheory.Functor.IsPredeformationFunctor

/-- The `k`-linear map of tangent spaces of restricted coyoneda functors induced by a
morphism `f : R ⟶ S` in `CompleteLocalAlgCat Λ k`, given on underlying functions by the
dual-number component of `restrictedCoyonedaMap f`. -/
def tangentSpaceMap {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S) :
    tangentSpace (restrictedCoyoneda S) →ₗ[k] tangentSpace (restrictedCoyoneda R) where
  toFun := (restrictedCoyonedaMap f).app (ArtinianLocalAlgCat.dualNumber Λ k)
  map_add' := sorry
  map_smul' := sorry

/-- The underlying function of `tangentSpaceMap f` is the dual-number component of
`restrictedCoyonedaMap f`. -/
theorem tangentSpaceMap_apply {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S)
    (x : tangentSpace (restrictedCoyoneda S)) :
    tangentSpaceMap f x =
      (restrictedCoyonedaMap f).app (ArtinianLocalAlgCat.dualNumber Λ k) x :=
  sorry

end CategoryTheory.Functor.IsPredeformationFunctor

namespace CompleteLocalAlgCat

/-- Evaluating the square-zero component of `restrictedCoyonedaMap f` as a derivation is
restriction of `homToDerivation S V g` along the underlying algebra map of `f`. -/
theorem homToDerivation_restrictedCoyonedaMap {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S)
    (V : Type u) [AddCommGroup V] [Module k V] [Module Λ V] [IsScalarTower Λ k V]
    [Module.Finite k V]
    (g : S ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.squareZero Λ k V))
    (x : R.carrier) :
    homToDerivation R V
        ((restrictedCoyonedaMap f).app (ArtinianLocalAlgCat.squareZero Λ k V) g) x =
      homToDerivation S V g (f.hom x) :=
  sorry

end CompleteLocalAlgCat

end
