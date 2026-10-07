module

public import stacks_project.Chap74.Lemma_74_22_5_Coproduct
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u v

/- Lemma 74.22.5: for a scheme `S` and a small family `f i : Xᵢ i ⟶ X` of morphisms of
algebraic spaces over `S`, descent data relative to the family are canonically equivalent to
descent data relative to `Y ⟶ X` with `Y = coproduct Xᵢ`, via `V = coproduct` of the component
spaces `Vᵢ` and `φ = coproduct` of the pairwise comparisons `φᵢⱼ`. -/
@[stacks 0ADK] #check (AlgebraicGeometry.AlgebraicSpace.DescentData.coproductEquivalence :
    ∀ {I : Type v} [Small.{u} I] {S : Scheme.{u}} {X : AlgebraicSpace S}
      (Xᵢ : I → AlgebraicSpace S) (f : ∀ i, Xᵢ i ⟶ X),
      AlgebraicGeometry.AlgebraicSpace.DescentData Xᵢ f ≌
        AlgebraicGeometry.AlgebraicSpace.DescentData
          (AlgebraicGeometry.AlgebraicSpace.DescentData.coproductFamily Xᵢ)
          (AlgebraicGeometry.AlgebraicSpace.DescentData.coproductArrow Xᵢ f))

#check AlgebraicGeometry.AlgebraicSpace.DescentData.assembleCoproduct
#check AlgebraicGeometry.AlgebraicSpace.DescentData.restrictCoproduct
#check AlgebraicGeometry.AlgebraicSpace.DescentData.coproductEquivalence_obj
#check AlgebraicGeometry.AlgebraicSpace.DescentData.coproductEquivalence_hom_ι
