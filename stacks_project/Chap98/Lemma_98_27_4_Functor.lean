module

public import stacks_project.Chap98.Lemma_98_25_2_Noetherian
public import stacks_project.Chap98.Lemma_98_27_4_Triple

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.Functor

/-!
# The contraction functor

The rule `F` sending a locally Noetherian scheme `V` over `S` to the type of
compatible triples, and a morphism `φ : V2 ⟶ V1` to inverse image of the closed
subset, restriction of the open morphism, and completion of `φ`, is a
contravariant functor on `(locallyNoetherian S).FullSubcategory`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.Scheme.Over
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ContractionSituation.functor :
  ∀ {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    (σ : AlgebraicGeometry.AlgebraicSpace.ContractionSituation S),
    (AlgebraicGeometry.Scheme.Over.locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type (u + 1))
