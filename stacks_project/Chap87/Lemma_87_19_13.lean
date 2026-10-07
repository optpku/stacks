module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_19_13_Completion
public import stacks_project.Chap87.Lemma_87_19_13_Over
public import stacks_project.Chap87.Lemma_87_19_13_Functor

/-!
# Lemma 87.19.13

For a McQuillan affine formal algebraic space `Y = Spf(B)` over a scheme `S`,
morphisms `X ⟶ Y` of affine formal algebraic spaces that are representable by
algebraic spaces and étale are equivalent to étale `B`-algebras via
`A^∧ ↦ Spf(A^∧)`. In particular every such `X` is McQuillan.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AffineFormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

variable {S : Scheme.{u}} {B : Type u} [CommRing B] [TopologicalSpace B]
  [TopologicalRing.IsWeaklyAdmissibleRing B] (hB : Spec (.of B) ⟶ S)
  [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]

/-- Lemma 87.19.13 (1): Let `S` be a scheme. Let `Y` be a McQuillan affine
formal algebraic space over `S`, i.e., `Y = Spf(B)` for a weakly admissible
topological `S`-algebra `B`. Then `spfEtaleCompletion B hB` is an equivalence
between étale `B`-algebras `A` (with topological algebra `A^∧ = lim A ⧸ J A`
as `J` runs over weak ideals of definition of `B`) and morphisms
`X ⟶ Spf(B)` of affine formal algebraic spaces that are representable by
algebraic spaces and étale, sending `A^∧` to `X = Spf(A^∧)`. -/
@[stacks 0AN8]
instance instIsEquivalence_spfEtaleCompletion :
    (spfEtaleCompletion hB).IsEquivalence :=
  sorry

/-- Lemma 87.19.13 (2): In the situation of Lemma 87.19.13 (1), any morphism
`X ⟶ Spf(B)` of affine formal algebraic spaces that is representable by
algebraic spaces and étale has McQuillan domain, i.e. `X = Spf(A)` for a
weakly admissible topological `S`-algebra `A`. -/
@[stacks 0AN8]
theorem isMcQuillanAffine_of_affineEtaleOver
    (X : AffineEtaleOver (spf B hB).obj) :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : TopologicalRing.IsWeaklyAdmissibleRing A) (hA : Spec (.of A) ⟶ S),
      Nonempty (X.obj.left ≅ (spf A hA).obj) :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
