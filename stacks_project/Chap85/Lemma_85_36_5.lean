module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.ProperDerivedEquivalence
import StacksCheckRecall

/-!
# Lemma 85.36.5

If `a : U ⟶ X` is a proper hypercovering of an algebraic space `X` over a scheme
`S`, then `a⁻¹` induces an equivalence `D⁺(X_étale) ≌ D_𝒜⁺(U_étale)` with
quasi-inverse `Ra_*`, where `𝒜` is the weak Serre subcategory of cartesian
abelian sheaves on `U_étale` and `a` is the Section 85.32 spaces-étale
augmentation.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open scoped Simplicial

/- Lemma 85.36.5. Proper hypercovering descent identifies bounded-below derived
étale sheaves with objects having cartesian cohomology, by `a⁻¹` with quasi-inverse `Ra_*`. -/
@[stacks 0DHN] #check
  (AlgebraicGeometry.AlgebraicSpace.Simplicial.properPlusCartesianEquivalence :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      {U : SimplicialObject (AlgebraicSpace S)}
      (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) (ha : IsProperHypercovering a),
      DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) ≌
        DerivedCategory.Plus.CohomologyIn (EtaleCartesian.IsCartesianAbelian U))

#check AlgebraicGeometry.AlgebraicSpace.Simplicial.properPlusCartesianEquivalence_functor
#check AlgebraicGeometry.AlgebraicSpace.Simplicial.properPlusCartesianEquivalence_inverse
