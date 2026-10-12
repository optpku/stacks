/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap72.Definition_72_4_1_Integral
public import stacks_project.Chap72.Lemma_72_14_3_Geometrically

/-!
# Definition 72.14.1

An algebraic space over a field `k` is geometrically integral over `k` if every
field base change is integral.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {k : Type u} [Field k]

namespace GeometricallyIntegral

/-- Definition 72.14.1: an algebraic space `X` over a field `k` is geometrically integral
over `k` if the algebraic space `X_K` is integral for every field extension `K` of `k`. -/
@[stacks 0DMW]
theorem iff_isIntegral_baseChange (X : AlgebraicSpace (Spec (of k))) :
    GeometricallyIntegral X ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        IsIntegral (baseChange (Spec.map (ofHom (algebraMap k K))) X) :=
  sorry

end GeometricallyIntegral

end AlgebraicGeometry.AlgebraicSpace
