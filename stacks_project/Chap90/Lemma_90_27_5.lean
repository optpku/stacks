/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Groupoid.Rigidity
import StacksCheckRecall

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

/- Lemma 90.27.5: let `(U, R, s, t, c)` and `(U', R', s', t', c')` be
minimal smooth prorepresentable groupoids in functors on
`ArtinianLocalAlgCat Λ k`. If `φ : [U/R] ⟶ [U'/R']` is an equivalence of
categories cofibered in groupoids, then `φ` is an isomorphism. -/
@[stacks 06KR] #check (CategoryTheory.GroupoidInFunctors.isIso_of_isEquivalence_between :
  ∀ (G H : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)),
    [IsSmooth G.s G.t] → [IsProrepresentable G] → [IsMinimal G] →
    [IsSmooth H.s H.t] → [IsProrepresentable H] → [IsMinimal H] →
    ∀ (φ : BasedCategory.ofFunctor G.forget ⟶ BasedCategory.ofFunctor H.forget),
      [BasedFunctor.IsEquivalence φ] → IsIso φ)

/- If a morphism of minimal smooth prorepresentable groupoids in functors
induces an equivalence of quotients, then the object-functor component is an
isomorphism. -/
#check (CategoryTheory.GroupoidInFunctors.Hom.isIso_obj_of_isEquivalence_between :
  ∀ (G H : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)),
    [IsSmooth G.s G.t] → [IsProrepresentable G] → [IsMinimal G] →
    [IsSmooth H.s H.t] → [IsProrepresentable H] → [IsMinimal H] →
    ∀ (f : Hom G H),
      [BasedFunctor.IsEquivalence (Hom.toQuotientBasedFunctor f)] → IsIso f.obj)

/- If a morphism of minimal smooth prorepresentable groupoids in functors
induces an equivalence of quotients, then the arrow-functor component is an
isomorphism. -/
#check (CategoryTheory.GroupoidInFunctors.Hom.isIso_arrow_of_isEquivalence_between :
  ∀ (G H : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)),
    [IsSmooth G.s G.t] → [IsProrepresentable G] → [IsMinimal G] →
    [IsSmooth H.s H.t] → [IsProrepresentable H] → [IsMinimal H] →
    ∀ (f : Hom G H),
      [BasedFunctor.IsEquivalence (Hom.toQuotientBasedFunctor f)] → IsIso f.arrow)

end CategoryTheory.GroupoidInFunctors
