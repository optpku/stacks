module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.ProperCohomologicalDescent
import StacksCheckRecall

/-!
# Lemma 85.36.3

If `a : U ⟶ X` is a proper hypercovering of an algebraic space `X` over a scheme `S`,
then for every `K` in `D⁺(X_étale)` the canonical derived unit `K ⟶ Ra_*(a⁻¹ K)` is an
isomorphism, where `a` is the Section 85.32 spaces-étale augmentation.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open scoped Simplicial

/- Lemma 85.36.3. Let `S` be a scheme, `X` an algebraic space over `S`, `U` a
simplicial algebraic space over `S`, and `a : U ⟶ X` a proper hypercovering of
`X`. Then for `K` in `D⁺(X_étale)` the canonical derived unit
`K ⟶ Ra_*(a⁻¹ K)` is an isomorphism. Here `a : Sh(U_étale) ⟶ Sh(X_étale)` is the
Section 85.32 spaces-étale augmentation, and the map is
`(EtaleDerived.plusDerivedUnit a).app K`. -/
@[stacks 0DHL] #check
  (AlgebraicGeometry.AlgebraicSpace.Simplicial.properPlusDerivedUnit_app_isIso :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      {U : SimplicialObject (AlgebraicSpace S)}
      (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X)
      (ha : IsProperHypercovering a)
      (K : DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})),
      IsIso ((EtaleDerived.plusDerivedUnit a).app K))

/- The derived unit `𝟭 ⟶ a⁻¹ ⋙ Ra_*` is an isomorphism
when `a` is a proper hypercovering. -/
#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.properPlusDerivedUnit_isIso :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X)
    (ha : IsProperHypercovering a), IsIso (EtaleDerived.plusDerivedUnit a))
