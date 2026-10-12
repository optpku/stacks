/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Extension
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Exercise 111.38.4: for a field `k` and a projective scheme `X` over `k`, every morphism
`φ : Spec (ProjectiveLine.scheme k).functionField ⟶ X` over `k` factors as the canonical
generic-point morphism
`(ProjectiveLine.scheme k).fromSpecStalk (genericPoint (ProjectiveLine.scheme k))`
followed by a morphism `ψ : ProjectiveLine.scheme k ⟶ X` over `k`. Here
`(ProjectiveLine.scheme k).functionField` is the function field `K` of `𝐏¹_k`, and the
displayed `Spec(k(t)) ⟶ 𝐏¹_k` is `fromSpecStalk` at the generic point. -/
@[stacks 0DJ4] #check (AlgebraicGeometry.exists_hom_fromProjectiveLine :
  ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [Projective sX]
    (φ : Spec (ProjectiveLine.scheme k).functionField ⟶ X)
    (hφ : φ ≫ sX =
      (ProjectiveLine.scheme k).fromSpecStalk (genericPoint (ProjectiveLine.scheme k)) ≫
        ProjectiveLine.toSpec k),
    ∃ ψ : ProjectiveLine.scheme k ⟶ X,
      ψ ≫ sX = ProjectiveLine.toSpec k ∧
        (ProjectiveLine.scheme k).fromSpecStalk (genericPoint (ProjectiveLine.scheme k)) ≫
          ψ = φ)

end AlgebraicGeometry
