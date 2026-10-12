/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Lemma_90_27_4
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalences of minimal smooth prorepresentable quotients

An equivalence of quotients of minimal smooth prorepresentable groupoids in
functors on `C_Λ` is an isomorphism.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

noncomputable section

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.GroupoidInFunctors

/-- Lemma 90.27.5: let `(U, R, s, t, c)` and `(U', R', s', t', c')` be
minimal smooth prorepresentable groupoids in functors on
`ArtinianLocalAlgCat Λ k`. If `φ : [U/R] ⟶ [U'/R']` is an equivalence of
categories cofibered in groupoids, then `φ` is an isomorphism. -/
@[stacks 06KR]
theorem isIso_of_isEquivalence_between
    (G H : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] [IsMinimal G]
    [IsSmooth H.s H.t] [IsProrepresentable H] [IsMinimal H]
    (φ : BasedCategory.ofFunctor G.forget ⟶ BasedCategory.ofFunctor H.forget)
    [BasedFunctor.IsEquivalence φ] :
    IsIso φ := sorry

/-- If a morphism of minimal smooth prorepresentable groupoids in functors
induces an equivalence of quotients, then the object-functor component is an
isomorphism. -/
theorem Hom.isIso_obj_of_isEquivalence_between
    (G H : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] [IsMinimal G]
    [IsSmooth H.s H.t] [IsProrepresentable H] [IsMinimal H] (f : Hom G H)
    [BasedFunctor.IsEquivalence (toQuotientBasedFunctor f)] :
    IsIso f.obj := sorry

/-- If a morphism of minimal smooth prorepresentable groupoids in functors
induces an equivalence of quotients, then the arrow-functor component is an
isomorphism. -/
theorem Hom.isIso_arrow_of_isEquivalence_between
    (G H : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] [IsMinimal G]
    [IsSmooth H.s H.t] [IsProrepresentable H] [IsMinimal H] (f : Hom G H)
    [BasedFunctor.IsEquivalence (toQuotientBasedFunctor f)] :
    IsIso f.arrow := sorry

end CategoryTheory.GroupoidInFunctors
