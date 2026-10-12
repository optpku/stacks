/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import stacks_project.Chap90.Definition_90_3_1_Classical
public import stacks_project.Chap90.Example_90_15_3_Quotient
public import stacks_project.Chap90.Lemma_90_3_4_Length
public import stacks_project.Chap90.Remark_90_15_6_Hull
import StacksCheckRecall

/-!
# Hulls in the classical and separable cases

A hull is a versal formal object with bijective differential. In the classical
case, and whenever `k / residueImage Λ k` is separable, a predeformation functor
satisfying (S1), (S2) and finite-dimensionality of its tangent space admits a hull.
-/

@[expose] public section

open CategoryTheory Limits

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Remark 90.15.6 (1): a hull is a versal formal object `ξ` such that
`differential ξ : Derivation Λ ξ.base.carrier k → Functor.tangentSpace p` is an
isomorphism, i.e. `FormalObject.BijectiveDifferential ξ` holds. -/
@[stacks 06IY] #check FormalObject.IsHull

namespace CategoryTheory.Functor

/-- Remark 90.15.6 (2): if `F : ArtinianLocalAlgCat Λ k ⥤ Type u` is a predeformation
functor in the sense that `elementsProjection F` is a predeformation category, and this
associated cofibered set satisfies Schlessinger's (S1) and (S2) with
`tangentSpace (elementsProjection F)` finite-dimensional over `k`, then in the
classical case there exists a hull. These functor (S1)+(S2)+`FiniteDimensional`
conditions are identified with (H1)+(H2)+(H3) by Remark 90.13.5, so this recovers
Schlessinger's existence theorem. -/
@[stacks 06IY]
theorem exists_isHull (F : ArtinianLocalAlgCat Λ k ⥤ Type u)
    [IsPredeformationCategory (elementsProjection F)]
    [HasSchlessingerS2 (elementsProjection F)]
    (h_s1 : ∀ {x x1 x2 : elementsTotal F} (f1 : x1 ⟶ x) (f2 : x2 ⟶ x),
      Function.Surjective ((elementsProjection F).map f2).hom →
        ∃ (y : elementsTotal F) (π1 : y ⟶ x1) (π2 : y ⟶ x2),
          CommSq π1 π2 f1 f2 ∧
            IsPullback ((elementsProjection F).map π1) ((elementsProjection F).map π2)
              ((elementsProjection F).map f1) ((elementsProjection F).map f2))
    [AddCommGroup (tangentSpace (elementsProjection F))]
    [Module k (tangentSpace (elementsProjection F))]
    [FiniteDimensional k (tangentSpace (elementsProjection F))]
    [ArtinianLocalAlgCat.IsClassical Λ k] :
    ∃ ξ : FormalObject (elementsProjection F), FormalObject.IsHull ξ := sorry

/-- If `Algebra.IsSeparable (Algebra.residueImage Λ k) k`, then a predeformation functor
`F` whose `elementsProjection F` satisfies (S1), (S2) and finite-dimensionality of
`tangentSpace (elementsProjection F)` admits a hull. These are the functor
(S1)+(S2)+`FiniteDimensional` conditions identified with (H1)+(H2)+(H3) by
Remark 90.13.5. -/
theorem exists_isHull_of_isSeparable (F : ArtinianLocalAlgCat Λ k ⥤ Type u)
    [IsPredeformationCategory (elementsProjection F)]
    [HasSchlessingerS2 (elementsProjection F)]
    (h_s1 : ∀ {x x1 x2 : elementsTotal F} (f1 : x1 ⟶ x) (f2 : x2 ⟶ x),
      Function.Surjective ((elementsProjection F).map f2).hom →
        ∃ (y : elementsTotal F) (π1 : y ⟶ x1) (π2 : y ⟶ x2),
          CommSq π1 π2 f1 f2 ∧
            IsPullback ((elementsProjection F).map π1) ((elementsProjection F).map π2)
              ((elementsProjection F).map f1) ((elementsProjection F).map f2))
    [AddCommGroup (tangentSpace (elementsProjection F))]
    [Module k (tangentSpace (elementsProjection F))]
    [FiniteDimensional k (tangentSpace (elementsProjection F))]
    [Algebra.IsSeparable (Algebra.residueImage Λ k) k] :
    ∃ ξ : FormalObject (elementsProjection F), FormalObject.IsHull ξ := sorry

end CategoryTheory.Functor
