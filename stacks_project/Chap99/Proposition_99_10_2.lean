module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import stacks_project.Chap99.Lemma_99_5_2
public import stacks_project.Chap99.Lemma_99_10_1
public import stacks_project.Chap99.Lemma_99_11_6_Forget
public import stacks_project.Chap108.Lemma_108_4_8_Algebraic

/-!
# Proposition 99.10.2

If `f : X ⟶ B` is a flat, finitely presented, proper morphism of algebraic
spaces over a scheme `S`, then the Picard stack `Pic_{X/B}` is an algebraic
stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupScheme
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Picard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The natural 1-morphism `Pic_{X/B} ⟶ Coh_{X/B}` of categories fibred in
groupoids over `Over S`, sending a triple `(T, g, L)` to the same triple
viewed as a coherent sheaf. The underlying functor is `toCoh f`. -/
def toCohHom (f : X ⟶ B) [Flat f] [FinitePresentation f] [Proper f] :
    toGroupoids f ⟶ CohStack.toGroupoids f :=
  ofBasedFunctor (BasedFunctor.ofFunctor (toCoh f) (toCoh_p f))

/-- The underlying functor of `toCohHom` is the identity-on-triples functor
`toCoh`. -/
theorem toCohHom_toFunctor (f : X ⟶ B) [Flat f] [FinitePresentation f] [Proper f] :
    FiberedCategoryOver.Groupoids.toFunctor (toCohHom f) = toCoh f :=
  sorry

/-- `toCohHom` lies strictly over `Over S`. -/
theorem toCohHom_p (f : X ⟶ B) [Flat f] [FinitePresentation f] [Proper f] :
    FiberedCategoryOver.Groupoids.toFunctor (toCohHom f) ⋙ CohStack.p f = p f :=
  sorry

/-- Proposition 99.10.2: let `S` be a scheme and let `f : X ⟶ B` be a morphism
of algebraic spaces over `S`. If `f` is flat, of finite presentation, and
proper, then `Pic_{X/B}` is an algebraic stack over `S` in the sense of
Definition 94.12.1 at Hom-universe `u + 1`. -/
@[stacks 0D04]
instance instAlgebraicStack (f : X ⟶ B) [Flat f] [FinitePresentation f] [Proper f] :
    CohStack.AlgebraicStack (toGroupoids f) :=
  sorry

/-- `CohStack.AlgebraicStack (toGroupoids f)` is equivalent to the three clauses
of Definition 94.12.1: `p f` is a stack in groupoids over `(Sch/S)_fppf`, the
diagonal of `toGroupoids f` is representable by algebraic spaces, and there is a
scheme `U` over `S` with a surjective smooth 1-morphism
`Classifying.slice U ⟶ toGroupoids f`. -/
theorem algebraicStack_iff (f : X ⟶ B) :
    CohStack.AlgebraicStack (toGroupoids f) ↔
      IsStack.InGroupoids (Scheme.fppfTopology.over S) (p f) ∧
        Classifying.relativelyRepresentableByAlgebraicSpaces
          (CohStack.diagonal (toGroupoids f)) ∧
        ∃ (U : Over S) (π : Classifying.slice U ⟶ toGroupoids f),
          Classifying.Smooth π ∧ Classifying.Surjective π :=
  sorry

/-- An algebraic stack `toGroupoids f` admits a scheme `U` over `S` and a
surjective smooth 1-morphism `Classifying.slice U ⟶ toGroupoids f`. -/
theorem existsSmoothSurjectiveAtlas (f : X ⟶ B)
    [CohStack.AlgebraicStack (toGroupoids f)] :
    ∃ (U : Over S) (π : Classifying.slice U ⟶ toGroupoids f),
      Classifying.Smooth π ∧ Classifying.Surjective π :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Picard
