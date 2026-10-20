module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Hypercohomology.ClosedPoints
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/- Lemma 59.97.4: an unbounded derived object of abelian étale sheaves on a finite-type
scheme over a separably closed field, with cohomology supported in closed points, is zero
if and only if its hypercohomology vanishes in every integer degree. -/
@[stacks 0F1G] #check
  (AlgebraicGeometry.Scheme.Etale.isZero_iff_etaleDerivedHypercohomology_isZero_of_support_closedPoints :
    ∀ {K : Type u} [Field K] [IsSepClosed K] (X : SchemeOverField K) [Algebraic X]
      [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
      [IsGrothendieckAbelian.{u} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
      (Q : DerivedCategory (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}))
      (hsupp : DerivedCategory.cohomologyIn
        (AlgebraicGeometry.Scheme.Etale.supportSubsetClosedPoints X.left) Q),
      IsZero Q ↔ ∀ i : ℤ,
        IsZero ((AlgebraicGeometry.Scheme.Etale.hypercohomologyFunctor X.left i).obj Q))
