module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.EtaleQuotient

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u v

/- 106.13.9.1: the local maps descend to a unique global morphism to the
algebraic-space quotient, with the displayed squares commuting up to 2-isomorphism.
Here U is the small coproduct of Mi, P is the already-established relation R,
and the bottom maps are the canonical quotient summand maps. The relation
hypothesis expresses the preceding overlap factorization. Cartesianness is the
subsequent claim. -/
@[stacks 0DUU] #check (AlgebraicGeometry.AlgebraicStack.exists_toEtaleQuotient :
    ∀ {S : Scheme.{u}} {I : Type v} [Small.{u} I]
    (X : GroupoidsOver S) (Xi : I → GroupoidsOver S)
    [AlgebraicStack X] [∀ i, AlgebraicStack (Xi i)]
    (gi : ∀ i, Xi i ⟶ X) (Mi : I → Over S)
    (fi : ∀ i, Xi i ⟶ (AlgebraicSpace.ofOver (Mi i)).toGroupoids)
    [∀ i, Groupoids.Hom.Etale (gi i)]
    (hcover : (⋃ i, Set.range (AlgebraicStack.Points.map (gi i))) = Set.univ)
    (P : Scheme.PreRelation (Scheme.Coproduct.overMk Mi)) [P.IsEtaleEquivalenceRelation]
    (hoverlap : ∀ (T : Over S) (i j : I)
      (ai : GroupoidsOver.slice T ⟶ Xi i) (aj : GroupoidsOver.slice T ⟶ Xi j)
      (mi : T ⟶ Mi i) (mj : T ⟶ Mi j),
      Nonempty (ai ≫ gi i ≅ aj ≫ gi j) →
      Nonempty (ai ≫ fi i ≅ (AlgebraicSpace.ofOverSliceEquiv T).inv ≫
        AlgebraicSpace.toGroupoids.map (yoneda.map mi)) →
      Nonempty (aj ≫ fi j ≅ (AlgebraicSpace.ofOverSliceEquiv T).inv ≫
        AlgebraicSpace.toGroupoids.map (yoneda.map mj)) →
      P.pointRel T (mi ≫ Scheme.Coproduct.overι Mi i) (mj ≫ Scheme.Coproduct.overι Mi j)),
    ∃ f : X ⟶ P.etaleQuotientSpace.toGroupoids,
      (∀ i, Nonempty (gi i ≫ f ≅ fi i ≫ AlgebraicSpace.toGroupoids.map
        (Scheme.PreRelation.etaleQuotientSummand Mi P i))) ∧
      ∀ f' : X ⟶ P.etaleQuotientSpace.toGroupoids,
        (∀ i, Nonempty (gi i ≫ f' ≅ fi i ≫ AlgebraicSpace.toGroupoids.map
          (Scheme.PreRelation.etaleQuotientSummand Mi P i))) →
        Nonempty (f' ≅ f))
