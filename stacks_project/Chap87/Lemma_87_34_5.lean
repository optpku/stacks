module

public import stacks_project.Chap87.Lemma_87_34_5_Comparison

/-!
# Lemma 87.34.5

The opposite of the affine étale site of a McQuillan affine formal algebraic
space `Spf(A)` is equivalent to the category of étale `A`-algebras.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalRing
open AlgebraicGeometry.AffineFormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

variable {S : Scheme.{u}} {A : Type u} [CommRing A] [TopologicalSpace A]
  [TopologicalRing.IsWeaklyAdmissibleRing A] (hA : Spec (.of A) ⟶ S)
  [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]

/-- Lemma 87.34.5: Let `S` be a scheme. Let `X` be an affine formal algebraic
space over `S`. Assume `X` is McQuillan, i.e., equal to `Spf(A)` for some
weakly admissible topological `S`-algebra `A`. Then
`(AlgebraicSpace.affineEtaleSite (reduction (spf A hA).obj))ᵒᵖ` is equivalent
to `CommAlgCat.Etale A`. Objects correspond to weak-ideal completions
`weakIdealCompletion A B = lim B ⧸ J B` as `J` runs over weak ideals of
definition of `A`, and morphisms correspond to continuous `A`-algebra
homomorphisms. -/
@[stacks 0DEF]
def spfAffineEtaleOppEquiv :
    (AlgebraicSpace.affineEtaleSite (reduction (spf A hA).obj))ᵒᵖ ≌
      CommAlgCat.Etale.{u} A :=
  (spfAffineEtaleEquiv hA).leftOp

/-- The forward functor of `spfAffineEtaleOppEquiv` is the left opposite of
`spfAffineEtaleEquiv`. -/
@[simp]
theorem spfAffineEtaleOppEquiv_functor :
    (spfAffineEtaleOppEquiv hA).functor = (spfAffineEtaleEquiv hA).leftOp.functor :=
  sorry

/-- The inverse functor of `spfAffineEtaleOppEquiv` is the left opposite inverse of
`spfAffineEtaleEquiv`. -/
@[simp]
theorem spfAffineEtaleOppEquiv_inverse :
    (spfAffineEtaleOppEquiv hA).inverse = (spfAffineEtaleEquiv hA).leftOp.inverse :=
  sorry

/-- The inverse of `spfAffineEtaleOppEquiv` sends an étale `A`-algebra `B` to
the underlying object of `spfEtaleCompletionSite`. -/
theorem spfAffineEtaleOppEquiv_inverse_obj (B : CommAlgCat.Etale.{u} A) :
    ((spfAffineEtaleOppEquiv hA).inverse.obj B).unop =
      (spfEtaleCompletionSite hA).obj (op B) :=
  sorry

/-- Morphisms of étale `A`-algebras correspond to continuous `A`-algebra
homomorphisms of weak-ideal completions. -/
theorem spfAffineEtaleOppEquiv_hom_iff {B B' : CommAlgCat.Etale.{u} A}
    (φ : weakIdealCompletion A B →+* weakIdealCompletion A B')
    (hφ : Continuous φ)
    (hw :
      φ.comp (algebraMap A (weakIdealCompletion A B)) =
        algebraMap A (weakIdealCompletion A B')) :
    ∃! f : B ⟶ B', φ = weakIdealCompletion.map f.hom.hom :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
