module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleQuotient
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale

/-!
# Descent of morphisms to étale quotients

Compatible local morphisms on a small jointly covering étale family of algebraic
stacks descend to the algebraic-space quotient of a scheme étale equivalence relation.
-/

@[expose] public section

open CategoryTheory
open scoped Bicategory

universe u v

namespace AlgebraicGeometry.AlgebraicStack

/-- Local morphisms from a small jointly covering étale family of algebraic stacks
to schemes descend uniquely up to 2-isomorphism to the algebraic-space quotient
of an étale equivalence relation on the coproduct, provided the local morphisms
on every overlap factor through that relation. -/
theorem exists_toEtaleQuotient {S : Scheme.{u}} {I : Type v} [Small.{u} I]
    (X : GroupoidsOver S) (Xi : I → GroupoidsOver S)
    [AlgebraicStack X] [∀ i, AlgebraicStack (Xi i)]
    (gi : ∀ i, Xi i ⟶ X) (Mi : I → Over S)
    (fi : ∀ i, Xi i ⟶ (AlgebraicSpace.ofOver (Mi i)).toGroupoids)
    [∀ i, Groupoids.Hom.Etale (gi i)]
    (hcover : (⋃ i, Set.range (Points.map (gi i))) = Set.univ)
    (P : Scheme.PreRelation (Scheme.Coproduct.overMk Mi)) [P.IsEtaleEquivalenceRelation]
    (hoverlap : ∀ (T : Over S) (i j : I)
      (ai : GroupoidsOver.slice T ⟶ Xi i) (aj : GroupoidsOver.slice T ⟶ Xi j)
      (mi : T ⟶ Mi i) (mj : T ⟶ Mi j),
      Nonempty (ai ≫ gi i ≅ aj ≫ gi j) →
      Nonempty (ai ≫ fi i ≅ (AlgebraicSpace.ofOverSliceEquiv T).inv ≫
        AlgebraicSpace.toGroupoids.map (yoneda.map mi)) →
      Nonempty (aj ≫ fi j ≅ (AlgebraicSpace.ofOverSliceEquiv T).inv ≫
        AlgebraicSpace.toGroupoids.map (yoneda.map mj)) →
      P.pointRel T (mi ≫ Scheme.Coproduct.overι Mi i) (mj ≫ Scheme.Coproduct.overι Mi j)) :
    ∃ f : X ⟶ P.etaleQuotientSpace.toGroupoids,
      (∀ i, Nonempty (gi i ≫ f ≅ fi i ≫ AlgebraicSpace.toGroupoids.map
        (Scheme.PreRelation.etaleQuotientSummand Mi P i))) ∧
      ∀ f' : X ⟶ P.etaleQuotientSpace.toGroupoids,
        (∀ i, Nonempty (gi i ≫ f' ≅ fi i ≫ AlgebraicSpace.toGroupoids.map
          (Scheme.PreRelation.etaleQuotientSummand Mi P i))) →
        Nonempty (f' ≅ f) := sorry

end AlgebraicGeometry.AlgebraicStack
